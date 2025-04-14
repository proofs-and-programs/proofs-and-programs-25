import Lean

open Lean Meta Elab Term Tactic
/-!
# Lookup the type of a constant

We illustrate how to look up the type of a constant in the environment.
We can use the `getEnv` function to get the environment and then use the `find?` function to look up a constant by its name. The result is an optional value of type `ConstantInfo`. We can then use the `ppExpr` function to pretty-print the type of the constant.
-/
def getTypeM (name : Name) : MetaM <| Option Format := do
  let env ← getEnv
  env.find? name |>.mapM
    (fun d => ppExpr d.type)

def getTypeCore (name : Name) : CoreM <| Option Format :=
  getTypeM name |>.run'

#eval getTypeM ``Nat.succ_le_succ

def getProofM (name : Name) : MetaM <| Option Format := do
  let env ← getEnv
  match env.find? name with
  | none => return none
  | some info =>
    match info.value? with
    | some t => ppExpr t
    | none => return none

#eval getProofM ``Nat.succ_le_succ
#eval getTypeM ``Nat.rec
#eval getProofM ``Nat.rec


/-
inductive Lean.ConstantInfo : Type
number of parameters: 0
constructors:
Lean.ConstantInfo.axiomInfo : AxiomVal → ConstantInfo
Lean.ConstantInfo.defnInfo : DefinitionVal → ConstantInfo
Lean.ConstantInfo.thmInfo : TheoremVal → ConstantInfo
Lean.ConstantInfo.opaqueInfo : OpaqueVal → ConstantInfo
Lean.ConstantInfo.quotInfo : QuotVal → ConstantInfo
Lean.ConstantInfo.inductInfo : InductiveVal → ConstantInfo
Lean.ConstantInfo.ctorInfo : ConstructorVal → ConstantInfo
Lean.ConstantInfo.recInfo : RecursorVal → ConstantInfo
-/
#print ConstantInfo
