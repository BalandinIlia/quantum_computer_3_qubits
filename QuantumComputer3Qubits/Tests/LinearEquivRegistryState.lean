import QuantumComputer3Qubits.Formalization.LinearEquivRegistryState
import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates

namespace Test_LinearEquivRegistryState

noncomputable
abbrev tp := TensorProduct.tmul

theorem test1:
(LER.reg2_reg1reg1 CS.s00 = tp ℂ (CS.q 0) (CS.q 0)) ∧
(LER.reg2_reg1reg1 CS.s01 = tp ℂ (CS.q 0) (CS.q 1)) ∧
(LER.reg2_reg1reg1 CS.s10 = tp ℂ (CS.q 1) (CS.q 0)) ∧
(LER.reg2_reg1reg1 CS.s11 = tp ℂ (CS.q 1) (CS.q 1)) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2_reg1reg1]

theorem test2: ∀i: Fin 3,(
(LER.reg1i_reg1 i (CS.qi 0 i)) = CS.q 0 ∧
(LER.reg1i_reg1 i (CS.qi 1 i)) = CS.q 1) := by
  intro i
  fin_cases i
  all_goals apply And.intro
  all_goals simp [LER.reg1i_reg1]
  all_goals aesop

theorem test3(i₁ i₂: Fin 3)(ord: i₁ < i₂):
  (LER.reg2i_reg2 i₁ i₂ ord (CS.qqi 0 0 i₁ i₂ ord) = CS.s00) ∧
  (LER.reg2i_reg2 i₁ i₂ ord (CS.qqi 0 1 i₁ i₂ ord) = CS.s01) ∧
  (LER.reg2i_reg2 i₁ i₂ ord (CS.qqi 1 0 i₁ i₂ ord) = CS.s10) ∧
  (LER.reg2i_reg2 i₁ i₂ ord (CS.qqi 1 1 i₁ i₂ ord) = CS.s11) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2i_reg2, LER.reg1i_reg1]
  all_goals aesop

theorem test4(i₁ i₂: Fin 3)(ord: i₁ < i₂):
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (CS.qqi 0 0 i₁ i₂ ord)) =
      tp ℂ (CS.qi 0 i₁) (CS.qi 0 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (CS.qqi 0 1 i₁ i₂ ord)) =
      tp ℂ (CS.qi 0 i₁) (CS.qi 1 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (CS.qqi 1 0 i₁ i₂ ord)) =
      tp ℂ (CS.qi 1 i₁) (CS.qi 0 i₂) ∧
  (LER.reg2i_reg1ireg1i i₁ i₂ ord (CS.qqi 1 1 i₁ i₂ ord)) =
      tp ℂ (CS.qi 1 i₁) (CS.qi 1 i₂) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2i_reg1ireg1i]

theorem test5:
(LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 0 0 1 (by aesop)) (CS.qi 0 2))) = CS.s000 ∧
(LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 1 0 0 1 (by aesop)) (CS.qi 0 2))) = CS.s100 ∧
(LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 1 0 1 (by aesop)) (CS.qi 0 2))) = CS.s010 ∧
(LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 0 0 1 (by aesop)) (CS.qi 1 2))) = CS.s001 := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2ireg1i_reg3]

theorem test6:
(LER.reg2ireg1i_reg3 0 2 (by aesop) 1 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 0 0 2 (by aesop)) (CS.qi 0 1))) = CS.s000 ∧
(LER.reg2ireg1i_reg3 0 2 (by aesop) 1 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 1 0 0 2 (by aesop)) (CS.qi 0 1))) = CS.s100 ∧
(LER.reg2ireg1i_reg3 0 2 (by aesop) 1 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 1 0 2 (by aesop)) (CS.qi 0 1))) = CS.s001 ∧
(LER.reg2ireg1i_reg3 0 2 (by aesop) 1 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 0 0 2 (by aesop)) (CS.qi 1 1))) = CS.s010 := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2ireg1i_reg3]

theorem test7:
(LER.reg2ireg1i_reg3 1 2 (by aesop) 0 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 0 1 2 (by aesop)) (CS.qi 0 0))) = SE.s000 ∧
(LER.reg2ireg1i_reg3 1 2 (by aesop) 0 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 1 0 1 2 (by aesop)) (CS.qi 0 0))) = SE.s010 ∧
(LER.reg2ireg1i_reg3 1 2 (by aesop) 0 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 1 1 2 (by aesop)) (CS.qi 0 0))) = SE.s001 ∧
(LER.reg2ireg1i_reg3 1 2 (by aesop) 0 (by aesop) (by aesop)
                    (tp ℂ (CS.qqi 0 0 1 2 (by aesop)) (CS.qi 1 0))) = SE.s100 := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [LER.reg2ireg1i_reg3]
