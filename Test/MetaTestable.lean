import Lean
import Plausible.MetaTestable

open Plausible Plausible.MetaTestable  Lean Meta Elab Term

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
    | (some α, some β) => logInfo s!"Imp: {← ppExpr α}; {← ppExpr β}"
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

#check List.nil

#check MetaTestResult.failure

elab "mk_failure%" prop:term ";" pf:term ";" : term => do
  let prop ← elabType prop
  let notProp ← mkAppM ``Not #[prop]
  let pf ← elabTerm pf notProp
  let lst ← mkAppOptM ``List.nil #[mkConst ``String]
  let pfExpr := Lean.Expr.letE
    `pf_var
    (notProp)
    (pf)
    (Lean.Expr.app
      (Lean.Expr.const `Lean.Expr.fvar [])
      (Lean.Expr.app
        (Lean.Expr.const `Lean.FVarId.mk [])
        (Lean.Expr.app (Lean.Expr.const `Lean.Name.mkStr1 []) (Lean.Expr.lit (Lean.Literal.strVal "pf_var")))))
    false
  logInfo s!"{repr pfExpr}"
  mkAppOptM ``MetaTestResult.failure #[prop, pf, pfExpr, lst, mkConst ``Nat.zero]

set_option pp.proofs true in
#check mk_failure% False ; fun (x: False) ↦ x ;

elab "#expr" e:term : command =>
  Command.liftTermElabM  do
    let e ← elabTerm e none
    logInfo s!"{repr e}"
    logInfo s!"{← reduce e}"

#check Expr.fvar {name := `n}

/-
Lean.Expr.fvar (Lean.FVarId.mk (Lean.Name.mkStr1 "n"))
-/
#expr (
    let pf_var : Nat := 0
    Expr.fvar {name := `pf_var})
#expr Lean.mkConst ``Nat

#check Lean.Expr.fvar (Lean.FVarId.mk (Lean.Name.mkStr1 "n"))

#check Lean.Expr.mvar (Lean.MVarId.mk (Lean.Name.mkStr1 "n"))
