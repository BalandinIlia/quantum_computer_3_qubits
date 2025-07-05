import QuantumComputer3Qubits.Formalization.LinearEquivRegistryState
import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Tests.StateExamples

theorem test1:
(LER.reg2_reg1reg1 SE.s00 = TensorProduct.tmul ℂ SE.s0 SE.s0) ∧
(LER.reg2_reg1reg1 SE.s01 = TensorProduct.tmul ℂ SE.s0 SE.s1) ∧
(LER.reg2_reg1reg1 SE.s10 = TensorProduct.tmul ℂ SE.s1 SE.s0) ∧
(LER.reg2_reg1reg1 SE.s11 = TensorProduct.tmul ℂ SE.s1 SE.s1) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2_reg1reg1]

theorem test2: ∀i: Fin 3,(
(LER.reg1i_reg1 i (SE.si0 i)) = SE.s0 ∧
(LER.reg1i_reg1 i (SE.si1 i)) = SE.s1) := by
  intro i
  fin_cases i
  all_goals apply And.intro
  all_goals simp [LER.reg1i_reg1]
  all_goals aesop

theorem test3(i₁ i₂: Fin 3)(ord: i₁ < i₂):
  (LER.reg2i_reg2 i₁ i₂ ord (SE.si00 i₁ i₂ ord) = SE.s00) ∧
  (LER.reg2i_reg2 i₁ i₂ ord (SE.si01 i₁ i₂ ord) = SE.s01) ∧
  (LER.reg2i_reg2 i₁ i₂ ord (SE.si10 i₁ i₂ ord) = SE.s10) ∧
  (LER.reg2i_reg2 i₁ i₂ ord (SE.si11 i₁ i₂ ord) = SE.s11) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2i_reg2, LER.reg1i_reg1]
  all_goals aesop

theorem test4(i₁ i₂: Fin 3)(ord: i₁ < i₂):
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (SE.si00 i₁ i₂ ord)) =
      TensorProduct.tmul ℂ (SE.si0 i₁) (SE.si0 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (SE.si01 i₁ i₂ ord)) =
      TensorProduct.tmul ℂ (SE.si0 i₁) (SE.si1 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (SE.si10 i₁ i₂ ord)) =
      TensorProduct.tmul ℂ (SE.si1 i₁) (SE.si0 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (SE.si11 i₁ i₂ ord)) =
      TensorProduct.tmul ℂ (SE.si1 i₁) (SE.si1 i₂) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2i_reg1ireg1i]

/-
noncomputable
def reg2ireg1i_reg3(i1 i2: Fin 3)
        (ord: (i1 < i2))
        (i3: Fin 3)
        (neq1: ¬(i3=i1))
        (neq2: ¬(i3=i2)):
  (StateReg2Ind i1 i2 ord) ⊗[ℂ] (StateReg1Ind i3) ≃ₗ[ℂ] StateReg3 :=
  match i1, i2, i3 with
-/
