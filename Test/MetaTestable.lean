import Lean
import Plausible.MetaTestable

open Plausible Plausible.MetaTestable
open Lean Meta Elab Term Tactic

open Lean Elab Term in
elab "#decompose_prop" t:term : command =>
  Command.liftTermElabM  do
    let e ← elabType t
    match ← orProp? e with
    | (some α, some β) => logInfo s!"Or: {← ppExpr α}; {← ppExpr β}"
    | _ => pure ()
    match ← andProp? e with
    | (some α, some β) => logInfo s!"And: {← ppExpr α}; {← ppExpr β}"
    | _ => pure ()
    match ← existsProp? e with
    | (some α, some β) => logInfo s!"Exists: {← ppExpr α}; domain {← ppExpr β}"
    | _ => pure ()
    match ← forallProp? e with
    | (some α, some β) => logInfo s!"Forall: {← ppExpr α}; domain {← ppExpr β}"
    | _ => pure ()
    match ← impProp? e with
    | (some α, some β) => logInfo s!"Implies: {← ppExpr α}; {← ppExpr β}"
    | _ => pure ()
    match ← eqlProp? e with
    | some (α, a, b) => logInfo s!"Eq: {← ppExpr α}; {← ppExpr a} and {← ppExpr b}"
    | _ => pure ()
    match ← iffProp? e with
    | some (α, β) => logInfo s!"Iff: {← ppExpr α}; {← ppExpr β}"
    | _ => pure ()

/-- info: Forall: fun x => x = 0 ∨ x ≠ 0; domain Nat -/
#guard_msgs in
#decompose_prop ∀ (n: Nat), n = 0 ∨ n ≠ 0

/-- info: Forall: fun x => x = 0 ∨ x ≠ 0; domain Nat -/
#guard_msgs in
#decompose_prop NamedBinder "blah" <| ∀ (n: Nat), n = 0 ∨ n ≠ 0

/-- info: Or: 1 = 0; 2 ≠ 0 -/
#guard_msgs in
#decompose_prop 1 = 0 ∨ 2 ≠ 0

/-- info: And: 1 = 0; 2 ≠ 0 -/
#guard_msgs in
#decompose_prop 1 = 0 ∧ 2 ≠ 0

/-- info: Exists: fun n => n = 0 ∨ n ≠ 0; domain Nat -/
#guard_msgs in
#decompose_prop ∃ (n: Nat), n = 0 ∨ n ≠ 0

/--
info: Forall: fun x => 2 ≠ 0; domain 1 = 0
---
info: Implies: 1 = 0; 2 ≠ 0
-/
#guard_msgs in
#decompose_prop 1 = 0 →  2 ≠ 0


/-- info: Iff: 1 = 0; 2 ≠ 0 -/
#guard_msgs in
#decompose_prop 1 = 0 ↔   2 ≠ 0

#check MetaTestResult.failure


def eg_fail : MetaTestResult False :=
  @MetaTestResult.failure False (fun (x: False) ↦ x)
    (Lean.Expr.lam `x (Lean.Expr.const `False []) (Lean.Expr.bvar 0) (Lean.BinderInfo.default)) [] 0

def disproofExpr {p: Prop} : MetaTestResult p → MetaM Lean.Expr
  | MetaTestResult.failure _ pfExpr _ _  => do
    return pfExpr
  | _ =>
    throwError "disproofExpr: expected failure"

elab "disproof_expr_eg%" : term => do
  disproofExpr eg_fail

/-
fun x => x : False → False
-/
#check disproof_expr_eg%

elab "#expr" e:term : command =>
  Command.liftTermElabM  do
    let e ← elabTerm e none
    logInfo s!"{repr e}"
    logInfo s!"{← reduce e}"

elab "expr%" e:term : term => do
    let e ← elabTerm e none
    logInfo s!"{repr e}"
    logInfo s!"{← reduce e}"
    return e
--

structure MyType where
  x : Nat
  y : Nat
  h : x ≤ y
  deriving Repr

#check fun (x y : Nat) (h : x ≤ y) =>  expr% (MyType.mk x y h)

instance : Shrinkable MyType where
  shrink := fun ⟨x, y, _⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (fun (fst, snd) => ⟨fst, fst + snd, by omega⟩)

instance : SampleableExt MyType :=
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    return ⟨x, x + xyDiff, by omega⟩

set_option diagnostics true in
-- #eval MetaTestable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y

open Decorations Lean Elab Tactic

elab "mk_decorations" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  if let .app (.const ``Decorations.DecorationsOf _) body := goalType then
    closeMainGoal `mk_decorations (← Decorations.addDecorations body)


def de : Decorations.DecorationsOf (∀ a b : Nat, a ≤ b) := by mk_decorations

#print de

#synth MetaTestable <| (1: Nat) = 0

#synth Testable (NamedBinder "a" (∀ (a : Nat), a ≤ 1))

#synth MetaTestable (NamedBinder "a" (∀ (a : Nat), a ≤ 1))

#synth MetaTestable (NamedBinder "a" (∀ (a : Nat), NamedBinder "b" (∀ (b : Nat), a ≤ b)))

set_option pp.universes true in
#eval MetaTestable.check (∀ (_a : Nat), False) (propExpr := Lean.Expr.forallE `a (Lean.Expr.const `Nat []) (Lean.Expr.const `False []) (Lean.BinderInfo.default))

/-
AppBuilder for 'mkAppM', result contains metavariables
  SampleableExt Nat
-/
set_option pp.universes true in
#eval MetaTestable.check (∀ (a : Nat), a < 1) (propExpr := Lean.Expr.forallE `a (Lean.Expr.const `Nat []) (Lean.Expr.const `False []) (Lean.BinderInfo.default))


#eval MetaTestable.check (∀ (a b : Nat), a < b) (propExpr := (Lean.Expr.forallE
  `a
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `b
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `LT.lt [Level.succ Level.zero])
            (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLTNat []))
        (Lean.Expr.bvar 1))
      (Lean.Expr.bvar 0))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)))

set_option linter.unusedVariables false in
#eval MetaTestable.check (∀ (a b : Nat), a < 0) (propExpr := (Lean.Expr.forallE
  `a
  (Lean.Expr.const `Nat [])
  (Lean.Expr.forallE
    `b
    (Lean.Expr.const `Nat [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.const `LT.lt [Level.succ Level.zero])
            (Lean.Expr.const `Nat []))
          (Lean.Expr.const `instLTNat []))
        (Lean.Expr.bvar 1))
      (Lean.Expr.lit (Lean.Literal.natVal 0)))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)))

#expr ∀ (a b : Nat), a < b
#expr ∀ (a _b : Nat), a < 0

#check Lean.Expr.lit (Lean.Literal.natVal 0)

#expr Expr → MetaM (Option Expr)


elab "disprove%" t:term : term => do
  let tgt ← elabType t
  let cfg : Configuration := {}
  let (some code') ← disproveM? cfg tgt | throwError "disprove% failed"
  logInfo s!"disproof: {← ppExpr code'}; \ntype: {← ppExpr <| (← inferType code')}"
  return tgt

#check disprove% ∀ (a b : Nat), a < b

#check disprove% ∀ (a b : Nat), a < b ∨ b < a

#check disprove% False ∧ False

def eg {p: Prop}(h : ¬¬p) : p :=
  by
  by_cases h':p
  · exact h'
  · exfalso
    contradiction

/-
def eg : ∀ {p : Prop}, ¬¬p → p :=
fun {p} h => if h' : p then h' else False.elim (absurd h' h)
-/
#print eg
