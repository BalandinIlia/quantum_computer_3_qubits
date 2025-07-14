import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import QuantumComputer3Qubits.Formalization.ComplexUtil
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates
-- This file formalizes vector decomposition into base vectors.
-- This formalization has the following advantage against
-- orthonormal basis:
-- It is very hard to access particular basis vector values
-- for orthonormal basis while in this formalization vector
-- values are easily accessible.
-- On the other hand, this formalization (unlike basis) does
-- not provide neither linear independence of base vectors
-- nor their orthonormality.

-- DC means "decompose"
namespace DC

-- This structure means: any element of type T can be
-- decomposed into linear combination of N vectors
structure Decompose(N: ℕ)
                   (T: Type)
                   [AddCommMonoid T]
                   [Module ℂ T] where
-- base (not basis) vectors
bas: Fin N → T
-- proposition that any vector is decomposable into linear
-- combination of base vectors
prop: ∀t: T, ∃c: Fin N → ℂ,
    t = FS.fs (fun i: Fin N => (c i) • (bas i))

def Decompose2 := Decompose 2
def Decompose4 := Decompose 4
def Decompose8 := Decompose 8

open scoped TensorProduct

-- tp means "tensor product"
noncomputable
def tp_2_2{T1 T2: Type}
          [AddCommMonoid T1]
          [Module ℂ T1]
          [AddCommMonoid T2]
          [Module ℂ T2]
          (dc1: Decompose2 T1)
          (dc2: Decompose2 T2):
          Decompose4 (T1 ⊗[ℂ] T2) :=
{
  bas := fun i: Fin 4 => match i with
  | 0 => (TensorProduct.tmul ℂ (dc1.bas 0) (dc2.bas 0))
  | 1 => (TensorProduct.tmul ℂ (dc1.bas 0) (dc2.bas 1))
  | 2 => (TensorProduct.tmul ℂ (dc1.bas 1) (dc2.bas 0))
  | 3 => (TensorProduct.tmul ℂ (dc1.bas 1) (dc2.bas 1))

  prop := by
    intro t
    simp [FS.FS4]
    apply TensorProduct.induction_on
          (motive := fun x:(T1 ⊗[ℂ] T2) => ∃ c: Fin 4 → ℂ,
                      x = c 0 • dc1.bas 0 ⊗ₜ[ℂ] dc2.bas 0 +
                          c 1 • dc1.bas 0 ⊗ₜ[ℂ] dc2.bas 1 +
                          c 2 • dc1.bas 1 ⊗ₜ[ℂ] dc2.bas 0 +
                          c 3 • dc1.bas 1 ⊗ₜ[ℂ] dc2.bas 1)
    {
      exists (fun i: Fin 4 => 0)
      simp
    }
    {
      intro x y
      let ⟨cX, st_x⟩ := dc1.prop x
      let ⟨cY, st_y⟩ := dc2.prop y
      exists (fun i: Fin 4 =>
                  (cX (@Fin.mk 2 ((i:ℕ)/2) (by fin_cases i; all_goals aesop))) *
                  (cY (@Fin.mk 2 ((i:ℕ)%2) (by fin_cases i; all_goals aesop))))
      simp
      simp [FS.FS2] at st_x st_y
      rw [st_x]
      rw [st_y]
      simp [TensorProduct.tmul_add, TensorProduct.add_tmul]
      simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
      module
    }
    {
      intro x y
      intro ih1 ih2
      let ⟨cX, st_x⟩ := ih1
      let ⟨cY, st_y⟩ := ih2
      exists (fun i: Fin 4 => (cX i) + (cY i))
      rw [st_x]
      rw [st_y]
      module
    }
}

noncomputable
def tp_4_2{T1 T2: Type}
          [AddCommMonoid T1]
          [Module ℂ T1]
          [AddCommMonoid T2]
          [Module ℂ T2]
          (dc1: Decompose4 T1)
          (dc2: Decompose2 T2):
          Decompose8 (T1 ⊗[ℂ] T2) :=
{
  bas := fun i: Fin 8 => match i with
  | 0 => (TensorProduct.tmul ℂ (dc1.bas 0) (dc2.bas 0))
  | 1 => (TensorProduct.tmul ℂ (dc1.bas 0) (dc2.bas 1))
  | 2 => (TensorProduct.tmul ℂ (dc1.bas 1) (dc2.bas 0))
  | 3 => (TensorProduct.tmul ℂ (dc1.bas 1) (dc2.bas 1))
  | 4 => (TensorProduct.tmul ℂ (dc1.bas 2) (dc2.bas 0))
  | 5 => (TensorProduct.tmul ℂ (dc1.bas 2) (dc2.bas 1))
  | 6 => (TensorProduct.tmul ℂ (dc1.bas 3) (dc2.bas 0))
  | 7 => (TensorProduct.tmul ℂ (dc1.bas 3) (dc2.bas 1))

  prop := by
    intro t
    simp [FS.FS8]
    apply TensorProduct.induction_on
          (motive := fun x:(T1 ⊗[ℂ] T2) => ∃ c: Fin 8 → ℂ,
                      x = c 0 • dc1.bas 0 ⊗ₜ[ℂ] dc2.bas 0 +
                          c 1 • dc1.bas 0 ⊗ₜ[ℂ] dc2.bas 1 +
                          c 2 • dc1.bas 1 ⊗ₜ[ℂ] dc2.bas 0 +
                          c 3 • dc1.bas 1 ⊗ₜ[ℂ] dc2.bas 1 +
                          c 4 • dc1.bas 2 ⊗ₜ[ℂ] dc2.bas 0 +
                          c 5 • dc1.bas 2 ⊗ₜ[ℂ] dc2.bas 1 +
                          c 6 • dc1.bas 3 ⊗ₜ[ℂ] dc2.bas 0 +
                          c 7 • dc1.bas 3 ⊗ₜ[ℂ] dc2.bas 1)
    {
      exists (fun i: Fin 8 => 0)
      simp
    }
    {
      intro x y
      let ⟨cX, st_x⟩ := dc1.prop x
      let ⟨cY, st_y⟩ := dc2.prop y
      exists (fun i: Fin 8 =>
                  (cX (@Fin.mk 4 ((i:ℕ)/2) (by fin_cases i; all_goals aesop))) *
                  (cY (@Fin.mk 2 ((i:ℕ)%2) (by fin_cases i; all_goals aesop))))
      simp
      simp [FS.FS4, FS.FS2] at st_x st_y
      rw [st_x]
      rw [st_y]
      simp [TensorProduct.tmul_add, TensorProduct.add_tmul]
      simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
      module
    }
    {
      intro x y
      intro ih1 ih2
      let ⟨cX, st_x⟩ := ih1
      let ⟨cY, st_y⟩ := ih2
      exists (fun i: Fin 8 => (cX i) + (cY i))
      rw [st_x]
      rw [st_y]
      module
    }
}

-- decomposable for 0th qubit
def dc0: DC.Decompose2 (StateReg1Ind 0) :=
{
  bas := fun i: Fin 2 => match i with
  -- Quantum analog of a qubit containing 0
  | 0 => CS.qi 0 0
  -- Quantum analog of a qubit containing 1
  | 1 => CS.qi 1 0

  prop := by
    intro t
    exists fun i: Fin 2 => match i with
                           | 0 => t X1.a
                           | 1 => t X1.b
    ext i
    cases i
    all_goals simp [FS.FS2]
    all_goals simp [StateReg1Ind, CS.qi, HAdd.hAdd]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

-- decomposable for 1st qubit
def dc1: DC.Decompose2 (StateReg1Ind 1) :=
{
  bas := fun i: Fin 2 => match i with
  -- Quantum analog of a qubit containing 0
  | 0 => CS.qi 0 1
  -- Quantum analog of a qubit containing 1
  | 1 => CS.qi 1 1

  prop := by
    intro t
    exists fun i: Fin 2 => match i with
                           | 0 => t X2.a
                           | 1 => t X2.b
    ext i
    cases i
    all_goals simp [FS.FS2]
    all_goals simp [StateReg1Ind, CS.qi, HAdd.hAdd]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

-- decomposable for 2nd qubit
def dc2: DC.Decompose2 (StateReg1Ind 2) :=
{
  bas := fun i: Fin 2 => match i with
  -- Quantum analog of a qubit containing 0
  | 0 => CS.qi 0 2
  -- Quantum analog of a qubit containing 1
  | 1 => CS.qi 1 2

  prop := by
    intro t
    exists fun i: Fin 2 => match i with
                           | 0 => t X3.a
                           | 1 => t X3.b
    ext i
    cases i
    all_goals simp [FS.FS2]
    all_goals simp [StateReg1Ind, CS.qi, HAdd.hAdd]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

-- decomposable for 3-qubit registry state
noncomputable
def dsReg3: DC.Decompose8 StateReg3 :=
DC.tp_4_2 (StateReg2Ind 0 1 (by simp))
          (QubitInd 2)
          (DC.tp_2_2 (QubitInd 0)
                     (QubitInd 1)
                     dc0
                     dc1
          )
          dc2
