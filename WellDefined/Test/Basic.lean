import WellDefined
import TrustAnnotations

/-! Each rule of the walk, on definitions with a declared domain and statements using them. -/

namespace WellDefined.Test

@[domain (0 < n) "the predecessor of 0 is 0, by convention"]
def pred' (n : Nat) : Nat := n - 1

@[domain (b ≠ 0)]
def div' (a b : Nat) : Nat := a / b

-- a hypothesis in scope
theorem by_hyp (n : Nat) (h : 0 < n) : pred' n + 1 = n := by unfold pred'; omega
-- a discharger, from the hypotheses
theorem by_omega (n : Nat) (h : 2 ≤ n) : pred' n ≠ 0 := by unfold pred'; omega
-- nothing says so: open
theorem is_open (n : Nat) : pred' n ≤ n := by unfold pred'; omega
-- about the value outside the domain: refuted
theorem at_zero : pred' 0 = 0 := rfl
-- the left side of ∧ on its right
theorem left_of_and (n : Nat) : 0 < n ∧ pred' n < n := by sorry
-- the negation of the left side of ∨ on its right
theorem left_of_or (n : Nat) : n = 0 ∨ pred' n < n := by sorry
-- the condition of `if` in its branch
theorem in_ite (n : Nat) : (if 0 < n then pred' n else 0) ≤ n := by sorry
-- a hypothesis inside the statement, for what follows it
theorem inner_hyp : ∀ n : Nat, 0 < n → pred' n < n := by sorry
-- in a hypothesis: checked with the hypotheses before it only
theorem in_hyp (n : Nat) (h : pred' n = 3) : n = 4 := by sorry
-- a variable bound inside the statement
theorem bound_var (f : Nat → Nat) : (fun k => pred' (f k)) = fun k => pred' (f k) := rfl
-- used as a function
theorem unapplied : (pred' ∘ Nat.succ) 0 = 0 := rfl
-- two arguments, the domain about the second
theorem two_args (a : Nat) : div' a 2 ≤ a := by sorry
-- nested: the inner use is checked too
theorem nested (n : Nat) (h : 1 < n) : pred' (pred' n) < n := by sorry
-- repeated uses count once, and the statement says the same whatever value they take
theorem repeated (n : Nat) : pred' n = pred' n := rfl
-- the value does not matter: irrelevant
theorem times_zero (n : Nat) : 0 * pred' n = 0 := Nat.zero_mul _
-- it does, in a hypothesis
theorem hyp_matters (n : Nat) (h : pred' n = 0) : n ≤ 1 := by sorry

/--
info: WellDefined.Test.by_hyp:
  conclusion: pred' n, needs 0 < n: discharged by assumption (h)
-/
#guard_msgs in #well_defined by_hyp

/--
info: WellDefined.Test.by_omega:
  conclusion: pred' n, needs 0 < n: discharged by omega
-/
#guard_msgs in #well_defined by_omega

/--
info: WellDefined.Test.is_open:
  conclusion: pred' n, needs 0 < n: open
-/
#guard_msgs in #well_defined is_open

/--
info: WellDefined.Test.at_zero:
  conclusion: pred' 0, needs 0 < 0: refuted by omega
-/
#guard_msgs in #well_defined at_zero

/--
info: WellDefined.Test.left_of_and:
  conclusion: pred' n, needs 0 < n: discharged by assumption (the left side of ∧)
-/
#guard_msgs in #well_defined left_of_and

/--
info: WellDefined.Test.left_of_or:
  conclusion: pred' n, needs 0 < n: discharged by omega
-/
#guard_msgs in #well_defined left_of_or

/--
info: WellDefined.Test.in_ite:
  conclusion: pred' n, needs 0 < n: discharged by assumption (the condition of if)
-/
#guard_msgs in #well_defined in_ite

/--
info: WellDefined.Test.inner_hyp:
  conclusion: pred' n, needs 0 < n: discharged by assumption
-/
#guard_msgs in #well_defined inner_hyp

/--
info: WellDefined.Test.in_hyp:
  hypothesis h: pred' n, needs 0 < n: open
-/
#guard_msgs in #well_defined in_hyp

/--
info: WellDefined.Test.bound_var:
  conclusion: pred' (f k), needs 0 < f k, for every k: open
-/
#guard_msgs in #well_defined bound_var

/--
info: WellDefined.Test.unapplied:
  conclusion: pred': unapplied
-/
#guard_msgs in #well_defined unapplied

/--
info: WellDefined.Test.two_args:
  conclusion: div' a 2, needs 2 ≠ 0: discharged by omega
-/
#guard_msgs in #well_defined two_args

/--
info: WellDefined.Test.nested:
  conclusion: pred' (pred' n), needs 0 < pred' n: open
  conclusion: pred' n, needs 0 < n: discharged by omega
-/
#guard_msgs in #well_defined nested

/--
info: WellDefined.Test.repeated:
  conclusion: pred' n, needs 0 < n: irrelevant by omega
-/
#guard_msgs in #well_defined repeated

/--
info: WellDefined.Test.times_zero:
  conclusion: pred' n, needs 0 < n: irrelevant by omega
-/
#guard_msgs in #well_defined times_zero

/--
info: WellDefined.Test.hyp_matters:
  hypothesis h: pred' n, needs 0 < n: open
-/
#guard_msgs in #well_defined hyp_matters
