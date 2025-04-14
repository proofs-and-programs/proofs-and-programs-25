import Lean
import Mathlib
import PfsProgs25.Unit13.CustomSorry
import Qq
open Qq
/-!
Given the expression of a term, we can try to directly match it, and there are helpers for this. But there is a smarter way using Lean's unification function `isDefEq`.

The function `isDefEq` takes two terms and returns a `MetaM Bool`. It returns true if the two terms are definitionally equal. More interestingly, if the terms have metavariables, it will try to solve them.
-/
open Lean Meta Elab Term Tactic

/-
Lean.Expr.isAppOfArity : Expr → Name → Nat → Bool
-/
#check Expr.isAppOfArity

/-
Lean.Expr.app3? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr)
-/
#check Expr.app3?

#check LE.le

#expr [(1 : Nat) ≤  2]

#expr [Nat.le 1  2]

def leExpr? (e: Expr) : Option (Expr × Expr × Expr) :=
  match e.app4? ``LE.le with
  | some (a, _, b, c) => some (a, b, c)
  | _ => none

elab "#leExpr" "[" e:term "]" : command =>
  Command.liftTermElabM do
  let e ← elabTerm e none
  match leExpr? e with
  | some (a, b, c) =>
    logInfo m!"{b} ≤ {c}; type {a}"
    logInfo m!"{b} has type: {← inferType b}"
    logInfo m!"{c} has type: {← inferType c}"
    logInfo m!"{a} has type: {← inferType a}"
    let check ← isDefEq (← inferType b) a
    logInfo m!"{b} has type {a}: {check}"
    Term.synthesizeSyntheticMVarsNoPostponing
    logInfo m!"{b} has type {a} (after synthesizing mvars)"
  | none => logInfo "Not a LE expression"

#leExpr [(1 : Nat) ≤  2]

#leExpr [(1 : ℕ) ≤  2]

#leExpr [1 ≤  2]

#expr [ℕ]

/-!
We will match in a smarted way:

* Create *metavariables* for the two terms, lhs and rhs.
* Create the expression `lhs ≤ rhs`.
* Equate this with the given expression and solve.
* Return the meta-variables.
-/
/-
⊢ Option Expr → optParam MetavarKind MetavarKind.natural → optParam Name Name.anonymous → MetaM Expr
-/
#check mkFreshExprMVar

def natLeExpr? (e: Expr) :
    MetaM (Option (Expr × Expr)) := do
  let natExpr :=  Lean.mkConst ``Nat
  let lhs ← mkFreshExprMVar natExpr
  let rhs ← mkFreshExprMVar natExpr
  let le ← mkAppM ``Nat.le #[lhs, rhs]
  if ← isDefEq e le then
    return some (lhs, rhs)
  else
    return none

elab "#natLeExpr"  e:term  : command =>
  Command.liftTermElabM do
  let e ← elabTerm e none
  match ← natLeExpr? e with
  | some (lhs, rhs) =>
    logInfo m!"{lhs} ≤ {rhs}"
    logInfo m!"{lhs} has type: {← inferType lhs}"
    logInfo m!"{rhs} has type: {← inferType rhs}"
  | none => logInfo "Not a Nat ≤ expression"

#natLeExpr (1 : ℕ) ≤  2

#natLeExpr (1 : ℤ) ≤  2

#natLeExpr 1  ≤  2

#natLeExpr 1 cat jumped over the rat

elab "#leExprAss" "[" e:term "]" : command =>
  Command.liftTermElabM do
  let e ← elabTerm e none
  match leExpr? e with
  | some (a, b, c) =>
    logInfo m!"{b} ≤ {c}; type {a}"
    logInfo m!"{b} has type: {← inferType b}"
    logInfo m!"{c} has type: {← inferType c}"
    logInfo m!"{a} has type: {← inferType a}"
    let check ← isDefEq (← inferType b) a
    logInfo m!"{b} has type {a}: {check}"
    let aId := a.mvarId!
    unless ← aId.isAssigned do
      let natExpr ← mkConst ``Nat
      aId.assign <| natExpr
    logInfo m!"{a} is now assigned, has type {← inferType a}"
    logInfo m!"{b} has type {← inferType b} (after assigning)"
  | none => logInfo "Not a LE expression"

#check MVarId.isAssigned
#check MVarId.assign

#leExprAss [(1 : ℕ) ≤  2]

#leExprAss [1 ≤  2]

#check addDecl

#check mkConstWithLevelParams

#check mkConstWithFreshMVarLevels

/-!
We will experiment with universe meta-levels. We will create a list `[0]` as `List.cons 0 List.nil`.
-/

elab "list_eg" : term => do
  let zero ← mkConst ``Nat.zero
  let lstNil ← mkAppOptM ``List.nil #[mkConst ``Nat]
  let e ← mkAppM ``List.cons #[zero, lstNil]
  return e

#check list_eg

#eval list_eg

#check mkSort

/-
⊢ Type u → Type v → Type (max u v)
-/
#check Prod

def prodExpr? (e: Expr) :
  MetaM <|Option (Expr × Expr) := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let α  ← mkFreshExprMVar (mkSort <| Level.succ u)
  let β  ← mkFreshExprMVar (mkSort <| Level.succ v)
  let prod ← mkAppM ``Prod #[α, β]
  if ← isDefEq e prod then
    return some (α, β)
  else
    return none


elab "#prodExpr" "[" e:term "]" : command =>
  Command.liftTermElabM do
  let e ← elabTerm e none
  match ← prodExpr? e with
  | some (α, β) =>
    logInfo m!"{α} × {β}"
    logInfo m!"{α} has type: {← inferType α}"
    logInfo m!"{β} has type: {← inferType β}"
  | none => logInfo "Not a PProd expression"

#prodExpr [Nat × (Nat → Type)]
