import WellDefined
import TrustAnnotations

/-! Binders that bring something in scope, and the bodies of definitions with a declared domain. -/

namespace WellDefined.Test.Bodies

@[domain (0 < n) "the predecessor of 0 is 0, by convention"]
def pred' (n : Nat) : Nat := n - 1

/-! ### Binders -/

/-- A sum over a list, standing in for `∑ i ∈ s, f i`. -/
def bsum (l : List Nat) (f : Nat → Nat) : Nat := (l.map f).sum

-- `#well_defined_bsum thm`: as `#well_defined`, with `bsum`'s function binding a variable that is
-- in its list.
open Lean Elab Command in
elab "#well_defined_bsum " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let obs ← liftTermElabM do
    (Analyzer.new (← getEnv) { binders := #[{ const := ``bsum, fn := 1, brings := .mem 0 }] }).obligationsOf n
  logInfo m!"{n}:{String.join (obs.toList.map (s!"\n  " ++ ·.line))}"

theorem sum_pos (l : List Nat) (h : ∀ n ∈ l, 0 < n) : bsum l (fun n => pred' n) ≤ bsum l id := by
  sorry

-- without the rule, the variable is any number
/--
info: WellDefined.Test.Bodies.sum_pos:
  conclusion: pred' n, needs 0 < n, for every n: open
-/
#guard_msgs in #well_defined sum_pos
-- with it, it is one of the list's, and the hypothesis says those are positive
/--
info: WellDefined.Test.Bodies.sum_pos:
  conclusion: pred' n, needs 0 < n, for every n: discharged by simp_all
-/
#guard_msgs in #well_defined_bsum sum_pos

/-! ### Bodies -/

-- the declared domain is in scope
@[domain (0 < n)]
def succPred (n : Nat) : Nat := pred' n + 1
/--
info: WellDefined.Test.Bodies.succPred:
  body: pred' n, needs 0 < n: discharged by assumption (the declared domain)
-/
#guard_msgs in #well_defined succPred

-- not enough: at n = 1, `n - 1` is outside `pred'`'s domain
@[domain (0 < n)]
def predPred (n : Nat) : Nat := pred' (n - 1)
/--
info: WellDefined.Test.Bodies.predPred:
  body: pred' (n - 1), needs 0 < n - 1: open
-/
#guard_msgs in #well_defined predPred

-- where `pred'`'s domain fails (n = 0), its value does not matter: `0 * c = 0`
@[domain (n < 100)]
def timesPred (n : Nat) : Nat := n * pred' n
/--
info: WellDefined.Test.Bodies.timesPred:
  body: pred' n, needs 0 < n: irrelevant by simp_all
-/
#guard_msgs in #well_defined timesPred

-- the condition of `if` in scope
@[domain (n < 100)]
def guarded (n : Nat) : Nat := if n = 0 then 0 else pred' n
/--
info: WellDefined.Test.Bodies.guarded:
  body: pred' n, needs 0 < n: discharged by omega
-/
#guard_msgs in #well_defined guarded

-- by cases: the second case's pattern is in the domain, which gives `0 < n`
@[domain (fun n => n ≠ 1)]
def byCases : Nat → Nat
  | 0 => 0
  | n + 1 => pred' n
/--
info: WellDefined.Test.Bodies.byCases:
  body, case 2: pred' n, needs 0 < n: discharged by omega
-/
#guard_msgs in #well_defined byCases

-- recursive: the recursive call leaves the domain at n = 0
@[domain (fun n => 0 < n)]
def countDown : Nat → Nat
  | 0 => 0
  | n + 1 => countDown n + 1
/--
info: WellDefined.Test.Bodies.countDown:
  body, case 2: countDown n, needs 0 < n: open
-/
#guard_msgs in #well_defined countDown

end WellDefined.Test.Bodies
