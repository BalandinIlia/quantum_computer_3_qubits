import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Tests.StateExamples

namespace Test_RegistryState

-- check that modules are defined for all registry states
#synth Module ℂ StateReg1
#synth Module ℂ StateReg2
#synth Module ℂ (StateReg1Ind 1)
#synth Module ℂ (StateReg2Ind 0 2 (by simp))
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
  (IP.f SE.s00 SE.s01 = 0) ∧
  (IP.f SE.s00 SE.s10 = 0) ∧
  (IP.f SE.s00 SE.s11 = 0) ∧
  (IP.f SE.s01 SE.s00 = 0) ∧
  (IP.f SE.s01 SE.s10 = 0) ∧
  (IP.f SE.s01 SE.s11 = 0) ∧
  (IP.f SE.s10 SE.s01 = 0) ∧
  (IP.f SE.s10 SE.s00 = 0) ∧
  (IP.f SE.s10 SE.s11 = 0) ∧
  (IP.f SE.s11 SE.s01 = 0) ∧
  (IP.f SE.s11 SE.s10 = 0) ∧
  (IP.f SE.s11 SE.s00 = 0) := by
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
  (IP.f SE.s00 SE.s00 = 1) ∧
  (IP.f SE.s01 SE.s01 = 1) ∧
  (IP.f SE.s10 SE.s10 = 1) ∧
  (IP.f SE.s11 SE.s11 = 1) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [IP.f, IP.IPLeft, IP.IPRight]
