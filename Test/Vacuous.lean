import Plausible.Vacuous
open Lean Meta Elab

elab "prove_vacuous" type:term : term => do
  let p ← Term.elabType type
  let vacuous ← proveVacuous? p
  match vacuous with
  | some pf =>
    return pf
  | none =>
    logWarning m!"No vacuous proof found"
    return mkConst ``False

/--
info:
===================
Found a counter-example!
issue: 2 < 1 does not hold
(0 shrinks)
-------------------
---
info: Vacuous Implication. Hypothesis 2 < 1 is never satisfied
---
info: fun a => False.elim (of_decide_eq_false (Eq.refl false) a) : 2 < 1 → 1 ≤ 3
-/
#guard_msgs in
#check prove_vacuous ((2 : Nat) < 1) → 1 ≤ 3

/--
info:
===================
Found a counter-example!
n := 5
issue: 5 < 4 does not hold
(0 shrinks)
-------------------
---
info: Vacuous Implication. Hypothesis ∀ (n : Nat), n < 4 is never satisfied
---
info: fun a =>
  False.elim
    (mt (fun x => x (Plausible.SampleableExt.interp 5)) (of_decide_eq_false (Eq.refl false))
      a) : (∀ (n : Nat), n < 4) → 1 ≤ 3
-/
#guard_msgs in
#check prove_vacuous (∀ n: Nat, n < (4: Nat)) → 1 ≤ 3

/--
info:
===================
Found a counter-example!
n := 5
issue: 5 < 4 does not hold
(0 shrinks)
-------------------
---
info: Vacuous Implication. Hypothesis ∀ (n : Nat), n < 4 is never satisfied
-/
#guard_msgs in
-- Can negate hypothesis in goal statement
example : (∀ n: Nat, n < (4: Nat)) → 4 ≤ 3 := by vacuous

/--
info:
===================
Found a counter-example!
n := 5
issue: 5 < 4 does not hold
(0 shrinks)
-------------------
---
info: Vacuous Implication. Hypothesis ∀ (n : Nat), n < 4 is never satisfied
-/
#guard_msgs in
-- Can negate hypothesis in local context
example (h: ∀ n: Nat, n < (4: Nat)) : 4 ≤ 3 := by vacuous

/--
info:
===================
Found a counter-example!
n := 5
issue: 5 < 4 does not hold
(0 shrinks)
-------------------
---
info: Vacuous Implication. Hypothesis ∀ (n : Nat), n < 4 is never satisfied
-/
#guard_msgs in
-- Can negate hypothesis other than the first one
example (m: Nat) (h: ∀ n: Nat, n < (4: Nat)) : m ≤ 3 := by vacuous
