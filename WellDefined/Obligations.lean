import Lean
import TrustAnnotations

/-!
# Obligations: every use of a definition stays inside its declared domain

`well-definedness.md` §2.5 in LeanTrustBuilders/design, the *outside* obligation. The author of a
definition declares where it is meant to apply (`@[domain (0 < x)]`, from TrustAnnotations), and a
catalogue does the same for a library it cannot edit. Each application `d a₁ … aₙ` of such a
definition in a statement then carries an obligation: that `a₁ … aₙ` are in `d`'s domain, given
what is in scope where the application sits.

**What is in scope** is read the way Event-B computes well-definedness conditions:
* the theorem's hypotheses, for everything after them, and a hypothesis written inside the
  statement (`∀ x, 0 < x → …`) for what follows it;
* the left side of `∧` on its right, and the negation of the left side of `∨` on its right;
* the condition of an `if` in its first branch, and its negation in the second.

A variable bound inside the statement (`∫ x, Real.log (f x) ∂μ`) is in scope with no hypothesis
about it, so the obligation is about every value of it; the report says so (`bound`).

A domain that is a conjunction (`∃ hm : m ≤ m₀, SigmaFinite (μ.trim hm) ∧ Integrable f μ`, a
conjunction whose later parts depend on the first) gives one obligation per part, each with the
parts before it in scope: which part is left open is what a reader needs.

**How an obligation comes out:**
* `discharged`: proved from what is in scope, by a hypothesis or by one of the dischargers;
* `irrelevant`: the statement says the same whatever value the application takes. With the use
  replaced by a variable `c`, `∀ c, F[c] ↔ F` is proved, `F` being the hypothesis or conclusion it
  sits in, from the theorem's hypotheses alone (`0 * Real.log x = 0`);
* `refuted`: its negation is proved. The statement is about the definition outside its domain, as
  a lemma giving the value there is (`integral_undef`);
* `open`: neither. This is the statement's residual: what it leaves unsaid about the domain;
* `unapplied`: the definition is used as a function (`Tendsto Real.log …`), with too few arguments
  to state its domain.

**The dischargers are tactics, named as text** and parsed in the analyzed environment, so that
one runs only if the library imports it: `positivity` with Mathlib, `omega` anywhere. Each gets a
budget of heartbeats. The results depend on them, so a report names the dischargers it used.

Proofs and instances inside a statement are not walked: a use inside a proof term is that proof's
business, and instances are not where domains are left.
-/

open Lean Meta Elab TrustAnnotations

namespace WellDefined

/-- How an obligation came out. -/
inductive Status where
  /-- Proved from what is in scope. -/
  | discharged
  /-- The statement says the same whatever value the application takes. -/
  | irrelevant
  /-- Its negation is proved from what is in scope: the use is outside the domain. -/
  | refuted
  /-- Neither: what the statement leaves unsaid. -/
  | «open»
  /-- The definition is not applied to enough arguments to state its domain. -/
  | unapplied
deriving Repr, BEq, Inhabited

def Status.toString : Status → String
  | .discharged => "discharged" | .irrelevant => "irrelevant" | .refuted => "refuted"
  | .open => "open"
  | .unapplied => "unapplied"

/-- Where in a statement an application sits. -/
inductive Place where
  /-- In the type of one of the theorem's variables. -/
  | binder (name : String)
  /-- In the theorem's `index`-th hypothesis (from 1), named `name` unless it has no name. -/
  | hypothesis (name : String) (index : Nat)
  /-- In the conclusion. -/
  | conclusion
deriving Repr, BEq, Inhabited

def Place.toString : Place → String
  | .binder n => s!"binder {n}"
  | .hypothesis n i => if n.isEmpty then s!"hypothesis {i}" else s!"hypothesis {n}"
  | .conclusion => "conclusion"

/-- One application of a definition with a declared domain, and what became of its obligation. -/
structure Obligation where
  /-- The definition applied. -/
  op : Name
  /-- Who declared its domain: `"author"` or `"catalogue"`. -/
  source : String
  place : Place
  /-- The application, pretty-printed. -/
  term : String
  /-- The domain at the application, pretty-printed. Empty when `unapplied`. -/
  goal : String := ""
  status : Status
  /-- What decided it: `"assumption"` or a discharger's text. -/
  how? : Option String := none
  /-- The hypothesis that decided it, when one did and has a name. -/
  hypothesis? : Option String := none
  /-- The variables bound inside the statement that the obligation is about. -/
  bound : Array String := #[]
deriving Repr, Inhabited

/-! ## Configuration -/

structure Config where
  /-- The dischargers, as tactic text, tried in order after the hypotheses in scope. Those that do
  not parse in the analyzed environment are left out. -/
  dischargers : Array String :=
    #["omega", "infer_instance", "positivity", "fun_prop", "norm_num", "simp_all"]
  /-- The budget of each discharger on each obligation, in the unit of the option `maxHeartbeats`
  (thousands of heartbeats): a twentieth of Lean's default. -/
  heartbeats : Nat := 10000
  /-- Whether to try to prove the negation of what is not discharged. -/
  refute : Bool := true
deriving Repr, Inhabited

/-- A discharger, parsed. -/
structure Discharger where
  text : String
  stx : Syntax

/-- What an analysis needs, prepared once per environment. -/
structure Analyzer where
  cfg : Config
  domains : NameMap DomainEntry
  dischargers : Array Discharger

/-- The analyzer for `env`: its declared domains, and those of `cfg`'s dischargers that parse in
it. -/
def Analyzer.new (env : Environment) (cfg : Config := {}) : Analyzer :=
  { cfg
    domains := (domainEntries env).foldl (fun m d => m.insert d.decl d) {}
    dischargers := cfg.dischargers.filterMap fun t =>
      match Parser.runParserCategory env `tactic t with
      | .ok stx => some { text := t, stx }
      | .error _ => none }

/-! ## Discharging -/

/-- The conditions the walk brings in scope, named for a reader. -/
private def condition (n : Name) : Option String :=
  match n with
  | `_leftOfAnd => some "the left side of ∧"
  | `_notLeftOfOr => some "the left side of ∨ being false"
  | `_ifCondition => some "the condition of if"
  | `_ifNot => some "the condition of if being false"
  | `_part => some "part of a hypothesis"
  | _ => none

/-- The hypothesis in scope that states `goal` (up to reducible unfolding), by its name when it has
one a reader can see. `some none` when it has none. -/
private def hypothesisFor? (goal : Expr) : MetaM (Option (Option String)) := do
  let found ← (← getLCtx).findDeclRevM? fun d => do
    if d.isImplementationDetail then return none
    if ← withReducible (withNewMCtxDepth (isDefEq d.type goal)) then return some d
    return none
  return found.map fun d =>
    if let some s := condition d.userName then some s
    else if d.userName.hasMacroScopes then none else some d.userName.toString

/-- Whether the tactic `d` proves `goal` within `heartbeats` (as `maxHeartbeats` counts them), with
no `sorry`.
Leaves no trace: the state is restored whatever happens. -/
private def proves (goal : Expr) (d : Discharger) (heartbeats : Nat) : MetaM Bool := do
  let s ← saveState
  let ok ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats * 1000 }) do
        withCurrHeartbeats do
          let g ← mkFreshExprMVar goal
          let rest ← Term.TermElabM.run' <| Term.withoutErrToSorry <|
            Tactic.run g.mvarId! (Tactic.evalTactic d.stx)
          return rest.isEmpty && !(← instantiateMVars g).hasSorry)
    (fun _ => return false)
  s.restore
  return ok

/-- How `goal` is decided from what is in scope: by a hypothesis, or by the first discharger that
proves it. -/
private def decide? (a : Analyzer) (goal : Expr) :
    MetaM (Option (String × Option String)) := do
  if let some h ← hypothesisFor? goal then return some ("assumption", h)
  for d in a.dischargers do
    if ← proves goal d a.cfg.heartbeats then return some (d.text, none)
  return none

/-! ## The walk -/

private structure Ctx where
  analyzer : Analyzer
  place : Place := .conclusion
  /-- The hypothesis or conclusion being walked, with the theorem's variables and hypotheses in
  scope for it and nothing the walk brought in since. -/
  formula : Option (Expr × LocalContext × LocalInstances) := none
  /-- The variables bound inside the statement, as opposed to the theorem's own. -/
  bound : Array FVarId := #[]

private abbrev M := ReaderT Ctx <| StateRefT (Array Obligation) MetaM

private def text (e : Expr) : MetaM String :=
  return (← ppExpr e).pretty (width := 1000)

/-- The domain of `entry`'s definition at the arguments `args`, under the universes `us`: the
hidden predicate applied and unfolded. `none` when there are too few arguments. -/
private def domainAt (entry : DomainEntry) (us : List Level) (args : Array Expr) :
    MetaM (Option Expr) := do
  let some info := (← getEnv).find? entry.predicate | return none
  let arity := info.type.getForallBinderNames.length
  if args.size < arity then return none
  let goal := ((info.instantiateValueLevelParams! us).beta (args.extract 0 arity)).headBeta
  -- `∫ x, X 0 x ∂P` is `integral P (fun x => X 0 x)`: its domain reads, and is found, as
  -- `Integrable (X 0) P`
  return some (← Meta.transform goal (post := fun e => return .done e.eta))

/-- Whether the formula `f` says the same whatever value `e` takes: `∀ c, f[e := c] ↔ f`, proved by
a discharger in the context `lctx` of `f`. Only when `e` is about that context alone: a use under a
binder, or next to a condition the walk brought in scope, is not tried. -/
private def irrelevant? (a : Analyzer) (e f : Expr) (lctx : LocalContext)
    (insts : LocalInstances) : MetaM (Option String) := do
  if e.hasAnyFVar (!lctx.contains ·) then return none
  withLCtx lctx insts do
    let abst ← kabstract f e
    unless abst.hasLooseBVars do return none
    let goal := mkForall `c .default (← inferType e) (mkIff abst f)
    for d in a.dischargers do
      if ← proves goal d a.cfg.heartbeats then return some d.text
    return none

/-- Decides one part of the domain at `e`, and records it. -/
private def checkPart (e goal : Expr) (base : Obligation) : M Unit := do
  let ctx ← read
  let a := ctx.analyzer
  let bound ← ctx.bound.filterMapM fun x => do
    if goal.containsFVar x then return some (← x.getUserName).eraseMacroScopes.toString
    return none
  let o := { base with goal := ← text goal, bound }
  if let some (how, h) ← decide? a goal then
    modify (·.push { o with status := .discharged, how? := how, hypothesis? := h })
    return
  if let some (f, lctx, insts) := ctx.formula then
    if let some how ← irrelevant? a e f lctx insts then
      modify (·.push { o with status := .irrelevant, how? := how })
      return
  if a.cfg.refute then
    if let some (how, h) ← decide? a (mkNot goal) then
      modify (·.push { o with status := .refuted, how? := how, hypothesis? := h })
      return
  modify (·.push { o with status := .open })

/-- Decides each part of the domain `goal` at `e`: the parts of a conjunction in turn, each with the
ones before it in scope, including a proof of a proposition an `∃` binds. -/
private partial def checkParts (e goal : Expr) (base : Obligation) : M Unit := do
  let g ← whnfR goal
  if g.isAppOfArity ``And 2 then
    checkParts e g.appFn!.appArg! base
    withLocalDeclD `_leftOfAnd g.appFn!.appArg! fun _ => checkParts e g.appArg! base
  else if g.isAppOfArity ``Exists 2 then
    let dom := g.appFn!.appArg!
    if ← isProp dom then
      checkPart e dom base
      if let .lam n _ body _ := g.appArg! then
        withLocalDeclD n dom fun h => checkParts e (body.instantiate1 h) base
    else checkPart e goal base
  else checkPart e goal base

/-- Records the obligations of the application `e` of `c` to `args`. -/
private def check (e : Expr) (c : Name) (us : List Level) (args : Array Expr)
    (entry : DomainEntry) : M Unit := do
  let base : Obligation := { op := c, source := entry.source, place := (← read).place,
                             term := ← text e, status := .unapplied }
  let some goal ← domainAt entry us args | modify (·.push base); return
  checkParts e goal base

/-- Whether `e` is a proof. Unsure is taken as yes, so that the walk skips it. -/
private def isProof' (e : Expr) : MetaM Bool := do
  try isProof e catch _ => return true

/-- Runs `k` with the parts of a hypothesis `t` in scope as well: both sides of a conjunction, and
the witness and property of an existential, recursively. `∃ N, ∀ ω, τ ω ≤ N` then gives the bound
a lemma needs. -/
private partial def withParts (t : Expr) (k : M Unit) : M Unit := do
  let t' ← whnfR t
  if t'.isAppOfArity ``And 2 then
    let a := t'.appFn!.appArg!
    let b := t'.appArg!
    withLocalDeclD `_part a fun _ => withParts a <| withLocalDeclD `_part b fun _ => withParts b k
  else if t'.isAppOfArity ``Exists 2 then
    match t'.appArg! with
    | .lam n dom body _ =>
      withLocalDeclD n dom fun w => do
        let p := body.instantiate1 w
        withLocalDeclD `_part p fun _ => withParts p k
    | _ => k
  else k

mutual

/-- Walks a term inside a statement, with what is in scope. -/
private partial def walk (e : Expr) : M Unit := do
  match e with
  | .forallE n t b bi => walk t; intro n bi t b
  | .lam n t b bi => walk t; intro n bi t b
  | .letE n t v b _ =>
    walk t; walk v
    withLetDecl n t v fun x => walk (b.instantiate1 x)
  | .mdata _ b => walk b
  | .proj _ _ b => walk b
  | .app .. => walkApp e
  | .const c us =>
    if let some d := (← read).analyzer.domains.find? c then check e c us #[] d
  | _ => pure ()

/-- Brings a binder in scope for its body: a hypothesis when it is a proposition, a bound variable
otherwise. -/
private partial def intro (n : Name) (bi : BinderInfo) (t b : Expr) : M Unit :=
  withLocalDecl n bi t fun x => do
    if ← isProp t then withParts t (walk (b.instantiate1 x))
    else withReader (fun c => { c with bound := c.bound.push x.fvarId! }) (walk (b.instantiate1 x))

/-- Walks an application: the connectives that bring something in scope, then the definitions
with a domain, then the arguments that are neither proofs nor instances. -/
private partial def walkApp (e : Expr) : M Unit := do
  let args := e.getAppArgs
  if e.isAppOfArity ``And 2 then
    walk args[0]!
    withLocalDeclD `_leftOfAnd args[0]! fun _ => walk args[1]!
    return
  if e.isAppOfArity ``Or 2 then
    walk args[0]!
    withLocalDeclD `_notLeftOfOr (mkNot args[0]!) fun _ => walk args[1]!
    return
  if e.isAppOfArity ``ite 5 then
    walk args[1]!
    withLocalDeclD `_ifCondition args[1]! fun _ => walk args[3]!
    withLocalDeclD `_ifNot (mkNot args[1]!) fun _ => walk args[4]!
    return
  let f := e.getAppFn
  match f with
  | .const c us =>
    if let some d := (← read).analyzer.domains.find? c then check e c us args d
  | _ => walk f
  let info ← try getFunInfoNArgs f args.size catch _ => return
  for h : i in [:args.size] do
    if info.paramInfo[i]?.any (·.isInstImplicit) then continue
    if ← isProof' args[i] then continue
    walk args[i]

end

/-- Walks a statement: its variables and hypotheses, each in scope for what follows, then its
conclusion. `hyps` counts the hypotheses seen so far. -/
private partial def walkStatement (e : Expr) (hyps : Nat := 0) : M Unit := do
  match e with
  | .forallE n t b bi =>
    let hyp ← isProp t
    let name := if n.hasMacroScopes then "" else n.toString
    let hyps := if hyp then hyps + 1 else hyps
    let lctx ← getLCtx
    let insts ← getLocalInstances
    withReader (fun c => { c with place := if hyp then .hypothesis name hyps else .binder name
                                  formula := if hyp then some (t, lctx, insts) else none })
      (walk t)
    withLocalDecl n bi t fun x =>
      if hyp then withParts t (walkStatement (b.instantiate1 x) hyps)
      else walkStatement (b.instantiate1 x) hyps
  | .mdata _ b => walkStatement b hyps
  | _ =>
    let lctx ← getLCtx
    let insts ← getLocalInstances
    withReader (fun c => { c with place := .conclusion, formula := some (e, lctx, insts) }) (walk e)

/-! ## Entry points -/

/-- The obligations of the statement `type`: one per application of a definition with a declared
domain, repeated applications counted once. -/
def Analyzer.obligationsOfType (a : Analyzer) (type : Expr) : MetaM (Array Obligation) := do
  if a.domains.isEmpty || !type.getUsedConstants.any a.domains.contains then return #[]
  let (_, obs) ← ((walkStatement type).run { analyzer := a }).run #[]
  let mut seen : Std.HashSet (String × String × String × String) := {}
  let mut out := #[]
  for o in obs do
    let key := (o.op.toString, o.place.toString, o.term, o.goal)
    unless seen.contains key do
      seen := seen.insert key
      out := out.push o
  return out

/-- The obligations of the declaration `decl`'s statement, printed from inside its namespace as its
source reads (`Integrable f μ` for a theorem in `MeasureTheory`), as the extractor prints
statements. -/
def Analyzer.obligationsOf (a : Analyzer) (decl : Name) : MetaM (Array Obligation) := do
  let type := (← getConstInfo decl).type
  withTheReader Core.Context (fun c => { c with currNamespace := decl.getPrefix }) do
    a.obligationsOfType type

/-! ## Reports -/

def Place.fields : Place → List (String × Json)
  | .binder n => [("place", ("binder" : Json)), ("name", toJson n)]
  | .hypothesis n i => [("place", ("hypothesis" : Json)), ("name", toJson n), ("index", toJson i)]
  | .conclusion => [("place", ("conclusion" : Json))]

/-- An obligation as a row of the facet `welldefined/1`. -/
def Obligation.asJson (o : Obligation) : Json :=
  Json.mkObj <|
    [("kind", ("domain" : Json)), ("op", toJson o.op.toString), ("source", toJson o.source)] ++
    o.place.fields ++
    [("term", toJson o.term), ("goal", toJson o.goal), ("status", toJson o.status.toString)] ++
    (match o.how? with | some b => [("by", toJson b)] | none => []) ++
    (match o.hypothesis? with | some h => [("hypothesis", toJson h)] | none => []) ++
    (if o.bound.isEmpty then [] else [("bound", toJson o.bound)])

/-- One line per obligation, for a person. -/
def Obligation.line (o : Obligation) : String :=
  let how := match o.how?, o.hypothesis? with
    | some b, some h => s!" by {b} ({h})"
    | some b, none => s!" by {b}"
    | _, _ => ""
  let bound := if o.bound.isEmpty then "" else s!", for every {", ".intercalate o.bound.toList}"
  let goal := if o.goal.isEmpty then "" else s!", needs {o.goal}"
  s!"{o.place.toString}: {o.term}{goal}{bound}: {o.status.toString}{how}"

end WellDefined
