import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.QubitBasic
-- This file works with a qubit in quantum registry (QQR).
-- This file formalizes single QQR state and its attributes.
--
-- This file introduces types QubitInd. The main difference of
-- QubitInd from QubitState:
-- QubitState is a single qubit "in vacuum" while QubitInd is
-- a qubit in a 3-qubit registry. Formally this difference is
-- expressed in the definition: QubitState is just one type
-- while QubitInd is in fact "aggregator" of 3 types: separate
-- type for each qubit in the registry.
--
-- QubitInd uses QubitState attributes: for example inner
-- product: inner product is automatically trasferred from
-- QubitState to (QubitInd 0), (QubitInd 1), (QubitInd 2)
-- since they are linearly isomorphic types. QubitInd "lands"
-- QubitState into quantum registry of several qubits.

inductive X1
| a: X1
| b: X1

inductive X2
| a: X2
| b: X2

inductive X3
| a: X3
| b: X3

-- Type of a qubit in quantum registry
-- QubitInd 0 is the 0-th qubit in quantum registry
-- QubitInd 1 is the first qubit in quantum registry
-- QubitInd 2 is the second qubit in quantum registry
@[reducible]
def QubitInd(n: Fin 3):Type := match n with
| 0 => X1 → ℂ
| 1 => X2 → ℂ
| 2 => X3 → ℂ

@[reducible]
noncomputable
instance QubitIndMonoid(i:Fin 3):AddCommMonoid (QubitInd i) := match i with
| 0 => inferInstance
| 1 => inferInstance
| 2 => inferInstance
@[reducible]
noncomputable
instance QubitIndModule(i:Fin 3):Module ℂ (QubitInd i) := match i with
| 0 => inferInstance
| 1 => inferInstance
| 2 => inferInstance

-- Linear isomorphism between (QubitInd i) and QubitState.
-- This isomorphism allows to "transfer" QubitState attributes
-- such as inner product to (QubitInd i).
noncomputable
def isoQubitIndQubitBase(i: Fin 3): ((QubitInd i) ≃ₗ[ℂ] QubitState) :=
{
  toFun := fun (q:QubitInd i) =>
    match i with
    | 0 => fun x:Fin 2 => match x with
                          | 0 => q X1.a
                          | 1 => q X1.b
    | 1 => fun x:Fin 2 => match x with
                          | 0 => q X2.a
                          | 1 => q X2.b
    | 2 => fun x:Fin 2 => match x with
                          | 0 => q X3.a
                          | 1 => q X3.b
  invFun := fun (q:QubitState) =>
    match i with
    | 0 => fun x:X1 => match x with
                       | X1.a => q 0
                       | X1.b => q 1
    | 1 => fun x:X2 => match x with
                       | X2.a => q 0
                       | X2.b => q 1
    | 2 => fun x:X3 => match x with
                       | X3.a => q 0
                       | X3.b => q 1
  left_inv := by
    fin_cases i
    all_goals simp
    all_goals simp [Function.LeftInverse]
    all_goals intro x
    all_goals ext y
    all_goals cases y
    all_goals simp
  right_inv := by
    fin_cases i
    all_goals simp
    all_goals simp [Function.RightInverse, Function.LeftInverse]
    all_goals intro x
    all_goals ext y
    all_goals fin_cases y
    all_goals simp
  map_add' := by
    fin_cases i
    all_goals simp
    all_goals intro x y
    all_goals ext g
    all_goals fin_cases g
    all_goals simp [QubitInd]
  map_smul' := by
    fin_cases i
    all_goals simp
    all_goals intro m x
    all_goals ext g
    all_goals fin_cases g
    all_goals simp [QubitInd]
}

noncomputable
instance transferIPFromQubitBasicToQubit0:
  IP.Transfer (QubitInd 0) :=
{
  TB := QubitState
  instMon := inferInstance
  instMod := inferInstance
  instIP := inferInstance
  lE := isoQubitIndQubitBase 0
}
noncomputable
instance transferOBFromQubitBasicToQubit0:
    OB.OrthonormalBasisImpl (QubitInd 0) 2 :=
    OB.transferOrt (QubitInd 0) 2 QubitStateOrthonormalBasis

noncomputable
instance transferIPFromQubitBasicToQubit1:
  IP.Transfer (QubitInd 1) :=
{
  TB := QubitState
  instMon := inferInstance
  instMod := inferInstance
  instIP := inferInstance
  lE := isoQubitIndQubitBase 1
}
noncomputable
instance transferOBFromQubitBasicToQubit1:
    OB.OrthonormalBasisImpl (QubitInd 1) 2 :=
    OB.transferOrt (QubitInd 1) 2 QubitStateOrthonormalBasis

noncomputable
instance transferIPFromQubitBasicToQubit2:
  IP.Transfer (QubitInd 2) :=
{
  TB := QubitState
  instMon := inferInstance
  instMod := inferInstance
  instIP := inferInstance
  lE := isoQubitIndQubitBase 2
}
noncomputable
instance transferOBFromQubitBasicToQubit2:
    OB.OrthonormalBasisImpl (QubitInd 2) 2 :=
    OB.transferOrt (QubitInd 2) 2 QubitStateOrthonormalBasis

noncomputable
instance transferIPFromQubitBasicToQubitInd (i: Fin 3):
  IP.Transfer (QubitInd i) :=
match i with
| 0 => inferInstance
| 1 => inferInstance
| 2 => inferInstance
