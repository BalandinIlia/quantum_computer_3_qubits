import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.HermitianConjugation
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

lemma hjk(op1 op2: o3):
(op1 SE.s000 = op2 SE.s000) →
(op1 SE.s001 = op2 SE.s001) →
(op1 SE.s010 = op2 SE.s010) →
(op1 SE.s011 = op2 SE.s011) →
(op1 SE.s100 = op2 SE.s100) →
(op1 SE.s101 = op2 SE.s101) →
(op1 SE.s110 = op2 SE.s110) →
(op1 SE.s111 = op2 SE.s111) →
op1 = op2 := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  have t:∀s: StateReg3, op1 s = op2 s := by
    intro s
    let ⟨x1, ⟨x2, ⟨x3, ⟨x4, ⟨x5, ⟨x6, ⟨x7, ⟨x8, st_x⟩⟩⟩⟩⟩⟩⟩⟩ := DS.prop s
    rw [Eq.symm st_x]
    simp
    have l1: op1 DS.t1 = op2 DS.t1 := by
      simp [DS, ds8, ds4, ds2_0, ds2_1, ds2_2]
      let h := h1
      simp [SE.si0, SE.si1] at h
      apply h
    have l2: op1 DS.t2 = op2 DS.t2 := by
      simp [DS, ds8, ds4, ds2_0, ds2_1, ds2_2]
      let h := h2
      simp [SE.si0, SE.si1] at h
      apply h
    have l3: op1 DS.t3 = op2 DS.t3 := by
      simp [DS, ds8, ds4, ds2_0, ds2_1, ds2_2]
      let h := h3
      simp [SE.si0, SE.si1] at h
      apply h
    have l4: op1 DS.t4 = op2 DS.t4 := by
      simp [DS, ds8, ds4, ds2_0, ds2_1, ds2_2]
      let h := h4
      simp [SE.si0, SE.si1] at h
      apply h
    have l5: op1 DS.t5 = op2 DS.t5 := by
      simp [DS, ds8, ds4, ds2_0, ds2_1, ds2_2]
      let h := h5
      simp [SE.si0, SE.si1] at h
      apply h
    have l6: op1 DS.t6 = op2 DS.t6 := by
      simp [DS, ds8, ds4, ds2_0, ds2_1, ds2_2]
      let h := h6
      simp [SE.si0, SE.si1] at h
      apply h
    have l7: op1 DS.t7 = op2 DS.t7 := by
      simp [DS, ds8, ds4, ds2_0, ds2_1, ds2_2]
      let h := h7
      simp [SE.si0, SE.si1] at h
      apply h
    have l8: op1 DS.t8 = op2 DS.t8 := by
      simp [DS, ds8, ds4, ds2_0, ds2_1, ds2_2]
      let h := h8
      simp [SE.si0, SE.si1] at h
      apply h
    rw [l1, l2, l3, l4, l5, l6, l7, l8]
  aesop

-- oi means "operator indexed"
@[reducible]
def oi1(i1: Fin 3):Type :=
  (StateReg1Ind i1) →ₗ[ℂ] (StateReg1Ind i1)

@[reducible]
def oi2(i1 i2: Fin 3)(ord: (i1 < i2)):Type :=
  (StateReg2Ind i1 i2 ord) →ₗ[ℂ] (StateReg2Ind i1 i2 ord)
