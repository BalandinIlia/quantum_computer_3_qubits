import QuantumComputer3Qubits.Formalization.QubitBasic
import QuantumComputer3Qubits.Formalization.QubitIndexed
import QuantumComputer3Qubits.Formalization.RegistryState
-- This file defines isomorphisms between (sub)registry types
-- formalizing the same quantum system.

-- LER means "Linear Equivalence Registry"
namespace LER

open scoped TensorProduct

-- Registry of 1 qubit is physically one qubit. So here is
-- natural isomorphism between qubit state and 1-qubit registry
-- state.
noncomputable
def reg1_st: StateReg1 ≃ₗ[ℂ] QubitState :=
{
  toFun(s: StateReg1) := s
  invFun(s: QubitState) := s
  map_add' := by aesop
  map_smul' := by aesop
}

-- Combination of 2 1-qubit registries is physically 2-qubit
-- registry. So here is natural isomporphism between state
-- of 2-qubit registry (StateReg2) and state of composite
-- system of 2 1-qubit registries (StateReg1 ⊗[ℂ] StateReg1).
noncomputable
def reg2_reg1reg1: StateReg2 ≃ₗ[ℂ] (StateReg1 ⊗[ℂ] StateReg1) :=
{
  toFun(s: StateReg2) := s
  invFun(s: StateReg1 ⊗[ℂ] StateReg1) := s
  map_add' := by aesop
  map_smul' := by aesop
}

-- 1-qubit registry and 1-qubit subregistry is in fact the
-- same physical system, - 1 qubit. So here is natural
-- isomorphism between their states.
noncomputable
def reg1i_reg1(i: Fin 3): (StateReg1Ind i) ≃ₗ[ℂ] StateReg1 :=
match i with
| 0 => {
  toFun(s: StateReg1Ind 0) :=
    fun x:Fin 2 => match x with
                   | 0 => s X1.a
                   | 1 => s X1.b
  invFun(s: StateReg1) :=
    fun x:X1 => match x with
                | X1.a => s 0
                | X1.b => s 1
  map_add' := by aesop
  map_smul' := by aesop
  left_inv := by
    simp [Function.LeftInverse]
    aesop
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    aesop
  }
| 1 => {
  toFun(s: StateReg1Ind 1) :=
    fun x:Fin 2 => match x with
                   | 0 => s X2.a
                   | 1 => s X2.b
  invFun(s: StateReg1) :=
    fun x:X2 => match x with
                | X2.a => s 0
                | X2.b => s 1
  map_add' := by aesop
  map_smul' := by aesop
  left_inv := by
    simp [Function.LeftInverse]
    aesop
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    aesop
  }
| 2 => {
  toFun(s: StateReg1Ind 2) :=
    fun x:Fin 2 => match x with
                   | 0 => s X3.a
                   | 1 => s X3.b
  invFun(s: StateReg1) :=
    fun x:X3 => match x with
                | X3.a => s 0
                | X3.b => s 1
  map_add' := by aesop
  map_smul' := by aesop
  left_inv := by
    simp [Function.LeftInverse]
    aesop
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    aesop
  }

-- Natural isomorphism between types representing the same
-- physical system.
noncomputable
def reg2i_reg2(i1 i2: Fin 3)(ord: i1 < i2):
  (StateReg2Ind i1 i2 ord) ≃ₗ[ℂ] StateReg2 :=
    TensorProduct.congr (reg1i_reg1 i1) (reg1i_reg1 i2)

-- Natural isomorphism between types representing the same
-- physical system.
noncomputable
def reg2i_reg1ireg1i(i1 i2: Fin 3)(ord: i1 < i2):
  (StateReg2Ind i1 i2 ord) ≃ₗ[ℂ] (StateReg1Ind i1) ⊗[ℂ] (StateReg1Ind i2) :=
{
  toFun(s: StateReg2Ind i1 i2 ord) := s
  invFun(s: (StateReg1Ind i1) ⊗[ℂ] (StateReg1Ind i2)) := s
  map_add' := by aesop
  map_smul' := by aesop
}

-- prove case by that that conditions on qubit indexes are
-- not met
macro "prove_not_met" : tactic =>
`(tactic|{
  apply False.elim;
  aesop
})

-- Natural isomorphism between types representing the same
-- physical system:
-- First type: type of composite system of disjoint 2-qubit
--             subregistry and 1-qubit subregistry (neq1 and neq2)
--             guarantee that subregistries are disjoint.
--             This composite system is, in fact 3-qubit registry.
-- Second type: state of 3-qubit registry
noncomputable
def reg2ireg1i_reg3(i1 i2: Fin 3)
                   (ord: (i1 < i2))
                   (i3: Fin 3)
                   (neq1: ¬(i3=i1))
                   (neq2: ¬(i3=i2)):
  (StateReg2Ind i1 i2 ord) ⊗[ℂ] (StateReg1Ind i3) ≃ₗ[ℂ] StateReg3 :=
  match i1, i2, i3 with
  | 0, 0, 0 => by prove_not_met
  | 0, 0, 1 => by prove_not_met
  | 0, 0, 2 => by prove_not_met
  | 0, 1, 0 => by prove_not_met
  | 0, 1, 1 => by prove_not_met
  | 0, 1, 2 => by
    clear i1 i2 i3
    clear neq1 neq2
    simp [StateReg1Ind, StateReg2Ind, StateReg3]
    clear ord
    exact LinearEquiv.refl ℂ ((QubitInd 0 ⊗[ℂ] QubitInd 1) ⊗[ℂ] QubitInd 2)
  | 0, 2, 0 => by prove_not_met
  | 0, 2, 1 => by
    clear i1 i2 i3
    clear neq1 neq2
    simp [StateReg1Ind, StateReg2Ind, StateReg3]
    clear ord

    -- Ts and Tf mean "Type start" and "Type finish".
    -- We need to define a linear isomorphism between Ts and Tf
    let Ts:Type := (QubitInd 0 ⊗[ℂ] QubitInd 2) ⊗[ℂ] QubitInd 1
    let Tf:Type := (QubitInd 0 ⊗[ℂ] QubitInd 1) ⊗[ℂ] QubitInd 2
    -- We use T1 and T2 as "intermediate points" on our way
    -- from Ts to Tf.
    -- More formally we define the following linear isomorphisms:
    -- Ts≃ₗT1, T1≃ₗT2, T2≃ₗTf and combine them into Ts≃ₗTf.
    let T1:Type := QubitInd 0 ⊗[ℂ] (QubitInd 2 ⊗[ℂ] QubitInd 1)
    let T2:Type := QubitInd 0 ⊗[ℂ] (QubitInd 1 ⊗[ℂ] QubitInd 2)

    have iso1: Ts ≃ₗ[ℂ] T1 := by
      simp [Ts, T1]
      exact TensorProduct.assoc ℂ (QubitInd 0) (QubitInd 2) (QubitInd 1)
    have iso2: T1 ≃ₗ[ℂ] T2 := by
      simp [T1, T2]
      let i1:QubitInd 2 ⊗[ℂ] QubitInd 1 ≃ₗ[ℂ] QubitInd 1 ⊗[ℂ] QubitInd 2 :=
        TensorProduct.comm ℂ (QubitInd 2) (QubitInd 1)
      let i2 := LinearEquiv.refl ℂ (QubitInd 0)
      exact TensorProduct.congr i2 i1
    have iso3: T2 ≃ₗ[ℂ] Tf := by
      let i:=TensorProduct.assoc ℂ (QubitInd 0) (QubitInd 1) (QubitInd 2)
      simp [T2, Tf]
      exact (LinearEquiv.symm i)
    have isoComp1: Ts ≃ₗ[ℂ] T2 := LinearEquiv.trans iso1 iso2
    have isoFin: Ts ≃ₗ[ℂ] Tf := LinearEquiv.trans isoComp1 iso3
    clear iso1 iso2 iso3 isoComp1 T1 T2

    exact isoFin
  | 0, 2, 2 => by prove_not_met
  | 1, 0, 0 => by prove_not_met
  | 1, 0, 1 => by prove_not_met
  | 1, 0, 2 => by prove_not_met
  | 1, 1, 0 => by prove_not_met
  | 1, 1, 1 => by prove_not_met
  | 1, 1, 2 => by prove_not_met
  | 1, 2, 0 => by
    clear i1 i2 i3 neq1 neq2
    simp [StateReg1Ind, StateReg2Ind, StateReg3]
    clear ord

    let Ts:Type := (QubitInd 1 ⊗[ℂ] QubitInd 2) ⊗[ℂ] (QubitInd 0)
    let Tf:Type := (QubitInd 0 ⊗[ℂ] QubitInd 1) ⊗[ℂ] (QubitInd 2)
    let T1:Type := (QubitInd 2 ⊗[ℂ] QubitInd 1) ⊗[ℂ] (QubitInd 0)
    let T2:Type := (QubitInd 2) ⊗[ℂ] (QubitInd 1 ⊗[ℂ] QubitInd 0)
    let T3:Type := (QubitInd 2) ⊗[ℂ] (QubitInd 0 ⊗[ℂ] QubitInd 1)

    have iso1: Ts ≃ₗ[ℂ] T1 := by
      simp [Ts, T1]
      let i1:QubitInd 1 ⊗[ℂ] QubitInd 2 ≃ₗ[ℂ] QubitInd 2 ⊗[ℂ] QubitInd 1 :=
        TensorProduct.comm ℂ (QubitInd 1) (QubitInd 2)
      let i2 := LinearEquiv.refl ℂ (QubitInd 0)
      exact TensorProduct.congr i1 i2
    have iso2: T1 ≃ₗ[ℂ] T2 := by
      simp [T1, T2]
      exact TensorProduct.assoc ℂ (QubitInd 2) (QubitInd 1) (QubitInd 0)
    have iso3: T2 ≃ₗ[ℂ] T3 := by
      simp [T2, T3]
      let i1:QubitInd 1 ⊗[ℂ] QubitInd 0 ≃ₗ[ℂ] QubitInd 0 ⊗[ℂ] QubitInd 1 :=
        TensorProduct.comm ℂ (QubitInd 1) (QubitInd 0)
      let i2 := LinearEquiv.refl ℂ (QubitInd 2)
      exact TensorProduct.congr i2 i1
    have iso4: T3 ≃ₗ[ℂ] Tf := by
      simp [T3, Tf]
      exact TensorProduct.comm ℂ (QubitInd 2) (QubitInd 0 ⊗[ℂ] QubitInd 1)

    have isoComp1: Ts ≃ₗ[ℂ] T2 := LinearEquiv.trans iso1 iso2
    have isoComp2: Ts ≃ₗ[ℂ] T3 := LinearEquiv.trans isoComp1 iso3
    exact LinearEquiv.trans isoComp2 iso4
  | 1, 2, 1 => by prove_not_met
  | 1, 2, 2 => by prove_not_met
  | 2, 0, 0 => by prove_not_met
  | 2, 0, 1 => by prove_not_met
  | 2, 0, 2 => by prove_not_met
  | 2, 1, 0 => by prove_not_met
  | 2, 1, 1 => by prove_not_met
  | 2, 1, 2 => by prove_not_met
  | 2, 2, 0 => by prove_not_met
  | 2, 2, 1 => by prove_not_met
  | 2, 2, 2 => by prove_not_met
