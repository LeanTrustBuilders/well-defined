import WellDefined
import TrustAnnotations

/-! Binders along which the body matters only eventually (`∫ x, … ∂μ`, `Tendsto`), with a stand-in for
Mathlib's `Filter.Eventually`: the analyzer knows it by name. -/

/-- A stand-in for Mathlib's `Filter.Eventually`: here, "for every element of a list". -/
def Filter.Eventually {α : Type} (p : α → Prop) (l : List α) : Prop := ∀ x ∈ l, p x

namespace WellDefined.Test.Eventually

@[domain (0 < n)]
def pred' (n : Nat) : Nat := n - 1

/-- A sum whose function matters only eventually along its list, as an integral's does almost
everywhere. -/
def evsum (l : List Nat) (f : Nat → Nat) : Nat := (l.map f).sum

open Lean Elab Command in
elab "#well_defined_ev " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let obs ← liftTermElabM do
    (Analyzer.new (← getEnv)
      { binders := #[{ const := ``evsum, fn := 1, brings := .eventually 0 }] }).obligationsOf n
  logInfo m!"{n}:{String.join (obs.toList.map (s!"\n  " ++ ·.line))}"

-- the obligation is needed only eventually, and a hypothesis says so
theorem ev_hyp (l : List Nat) (h : Filter.Eventually (fun n => 0 < n) l) :
    evsum l (fun n => pred' n) = 0 := by sorry
-- at every point implies eventually
theorem ev_everywhere (l : List Nat) (f : Nat → Nat) (h : ∀ n, 0 < f n) :
    evsum l (fun n => pred' (f n)) = 0 := by sorry
-- nothing says so
theorem ev_open (l : List Nat) : evsum l (fun n => pred' n) = 0 := by sorry

/--
info: WellDefined.Test.Eventually.ev_hyp:
  conclusion: pred' n, needs Filter.Eventually (fun n => 0 < n) l: discharged by assumption (h)
-/
#guard_msgs in #well_defined_ev ev_hyp

/--
info: WellDefined.Test.Eventually.ev_everywhere:
  conclusion: pred' (f n), needs Filter.Eventually (fun n => 0 < f n) l: discharged by simp_all, at every point
-/
#guard_msgs in #well_defined_ev ev_everywhere

/--
info: WellDefined.Test.Eventually.ev_open:
  conclusion: pred' n, needs Filter.Eventually (fun n => 0 < n) l: open
-/
#guard_msgs in #well_defined_ev ev_open

end WellDefined.Test.Eventually
