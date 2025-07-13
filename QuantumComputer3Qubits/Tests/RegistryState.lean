import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.ClassicalStates

namespace Test_RegistryState

-- check that modules are defined for all registry states
#synth Module ℂ StateReg1
#synth Module ℂ StateReg2
#synth Module ℂ (StateReg1Ind 0)
#synth Module ℂ (StateReg1Ind 1)
#synth Module ℂ (StateReg1Ind 2)
#synth Module ℂ (StateReg2Ind 0 1 (by simp))
#synth Module ℂ (StateReg2Ind 0 2 (by simp))
#synth Module ℂ (StateReg2Ind 1 2 (by simp))
#synth Module ℂ StateReg3

-- check that inner product is defined for all registry states
#synth IP StateReg1
#synth IP StateReg2
#synth IP (StateReg1Ind 1)
#synth IP (StateReg2Ind 0 2 (by simp))
#synth IP StateReg3

-- prove or-statement by proving left part
macro "pol": tactic =>
`(tactic|{
  apply Or.intro_left;
  simp [IP.f, QZero, QOne]
})

-- prove or-statement by proving right part
macro "por": tactic =>
`(tactic|{
  apply Or.intro_right;
  simp [IP.f, QZero, QOne]
})

-- prove or-statement
macro "po": tactic =>
`(tactic|{
  try pol;
  try por
})

theorem test1:
  (IP.f CS.s00 CS.s01 = 0) ∧
  (IP.f CS.s00 CS.s10 = 0) ∧
  (IP.f CS.s00 CS.s11 = 0) ∧
  (IP.f CS.s01 CS.s00 = 0) ∧
  (IP.f CS.s01 CS.s10 = 0) ∧
  (IP.f CS.s01 CS.s11 = 0) ∧
  (IP.f CS.s10 CS.s01 = 0) ∧
  (IP.f CS.s10 CS.s00 = 0) ∧
  (IP.f CS.s10 CS.s11 = 0) ∧
  (IP.f CS.s11 CS.s01 = 0) ∧
  (IP.f CS.s11 CS.s10 = 0) ∧
  (IP.f CS.s11 CS.s00 = 0) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [IP.f, IP.IPLeft, IP.IPRight]

theorem test2:
  (IP.f CS.s00 CS.s00 = 1) ∧
  (IP.f CS.s01 CS.s01 = 1) ∧
  (IP.f CS.s10 CS.s10 = 1) ∧
  (IP.f CS.s11 CS.s11 = 1) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [IP.f, IP.IPLeft, IP.IPRight]

#synth OrthonormalBasis StateReg1
#synth OrthonormalBasis StateReg2
#synth OrthonormalBasis (StateReg1Ind 0)
#synth OrthonormalBasis (StateReg1Ind 1)
#synth OrthonormalBasis (StateReg1Ind 2)
#synth OrthonormalBasis (StateReg2Ind 0 1 (by simp))
#synth OrthonormalBasis (StateReg2Ind 0 2 (by simp))
#synth OrthonormalBasis (StateReg2Ind 1 2 (by simp))
#synth OrthonormalBasis StateReg3
