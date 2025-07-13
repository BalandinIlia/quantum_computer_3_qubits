import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.Decompose
-- This file defines types of linear operators in different
-- (sub)registry linear spaces.

-- OP means "operator"
namespace OP

-- o means "operator"
@[reducible]
def o1: Type := StateReg1 →ₗ[ℂ] StateReg1

@[reducible]
def o2: Type := StateReg2 →ₗ[ℂ] StateReg2

@[reducible]
def o3: Type := StateReg3 →ₗ[ℂ] StateReg3

-- oi means "operator indexed"
@[reducible]
def oi1(i1: Fin 3):Type :=
  (StateReg1Ind i1) →ₗ[ℂ] (StateReg1Ind i1)

@[reducible]
def oi2(i1 i2: Fin 3)(ord: (i1 < i2)):Type :=
  (StateReg2Ind i1 i2 ord) →ₗ[ℂ] (StateReg2Ind i1 i2 ord)

lemma Equality3(op1 op2: o3):
(∀ v1 v2 v3: Fin 2, (op1 (CS.qqq v1 v2 v3) = op2 (CS.qqq v1 v2 v3))) →
op1 = op2 := by
  intro h
  have t:∀s: StateReg3, op1 s = op2 s := by
    intro s
    let ⟨cX, st_x⟩ := DC.dsReg3.prop s
    simp [FS.FS8, DC.dsReg3, DC.tp_4_2, DC.tp_2_2, DC.dc0, DC.dc1, DC.dc2] at st_x
    simp [st_x]
    simp [CS.qqq] at h
    simp [h]
  aesop
