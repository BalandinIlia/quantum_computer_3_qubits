import QuantumComputer3Qubits.Formalization.LinearEquivRegistryState
import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Tests.StateExamples

namespace Test_LinearEquivRegistryState

noncomputable
abbrev tp := TensorProduct.tmul

theorem test1:
(LER.reg2_reg1reg1 SE.s00 = tp ℂ SE.s0 SE.s0) ∧
(LER.reg2_reg1reg1 SE.s01 = tp ℂ SE.s0 SE.s1) ∧
(LER.reg2_reg1reg1 SE.s10 = tp ℂ SE.s1 SE.s0) ∧
(LER.reg2_reg1reg1 SE.s11 = tp ℂ SE.s1 SE.s1) := by
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
      tp ℂ (SE.si0 i₁) (SE.si0 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (SE.si01 i₁ i₂ ord)) =
      tp ℂ (SE.si0 i₁) (SE.si1 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (SE.si10 i₁ i₂ ord)) =
      tp ℂ (SE.si1 i₁) (SE.si0 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (SE.si11 i₁ i₂ ord)) =
      tp ℂ (SE.si1 i₁) (SE.si1 i₂) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2i_reg1ireg1i]

theorem test5:
(LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop)
                    (tp ℂ (SE.si00 0 1 (by aesop)) (SE.si0 2))) = SE.s000 ∧
(LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop)
                    (tp ℂ (SE.si10 0 1 (by aesop)) (SE.si0 2))) = SE.s100 ∧
(LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop)
                    (tp ℂ (SE.si01 0 1 (by aesop)) (SE.si0 2))) = SE.s010 ∧
(LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop)
                    (tp ℂ (SE.si00 0 1 (by aesop)) (SE.si1 2))) = SE.s001 := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2ireg1i_reg3]

theorem test6:
(LER.reg2ireg1i_reg3 0 2 (by aesop) 1 (by aesop) (by aesop)
                    (tp ℂ (SE.si00 0 2 (by aesop)) (SE.si0 1))) = SE.s000 ∧
(LER.reg2ireg1i_reg3 0 2 (by aesop) 1 (by aesop) (by aesop)
                    (tp ℂ (SE.si10 0 2 (by aesop)) (SE.si0 1))) = SE.s100 ∧
(LER.reg2ireg1i_reg3 0 2 (by aesop) 1 (by aesop) (by aesop)
                    (tp ℂ (SE.si01 0 2 (by aesop)) (SE.si0 1))) = SE.s001 ∧
(LER.reg2ireg1i_reg3 0 2 (by aesop) 1 (by aesop) (by aesop)
                    (tp ℂ (SE.si00 0 2 (by aesop)) (SE.si1 1))) = SE.s010 := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2ireg1i_reg3]

theorem test7:
(LER.reg2ireg1i_reg3 1 2 (by aesop) 0 (by aesop) (by aesop)
                    (tp ℂ (SE.si00 1 2 (by aesop)) (SE.si0 0))) = SE.s000 ∧
(LER.reg2ireg1i_reg3 1 2 (by aesop) 0 (by aesop) (by aesop)
                    (tp ℂ (SE.si10 1 2 (by aesop)) (SE.si0 0))) = SE.s010 ∧
(LER.reg2ireg1i_reg3 1 2 (by aesop) 0 (by aesop) (by aesop)
                    (tp ℂ (SE.si01 1 2 (by aesop)) (SE.si0 0))) = SE.s001 ∧
(LER.reg2ireg1i_reg3 1 2 (by aesop) 0 (by aesop) (by aesop)
                    (tp ℂ (SE.si00 1 2 (by aesop)) (SE.si1 0))) = SE.s100 := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2ireg1i_reg3]
