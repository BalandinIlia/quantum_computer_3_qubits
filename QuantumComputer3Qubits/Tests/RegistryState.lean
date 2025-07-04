import QuantumComputer3Qubits.Formalization.RegistryState

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

noncomputable
def st00: StateReg2 := TensorProduct.tmul ℂ QZero QZero
noncomputable
def st01: StateReg2 := TensorProduct.tmul ℂ QZero QOne
noncomputable
def st10: StateReg2 := TensorProduct.tmul ℂ QOne QZero
noncomputable
def st11: StateReg2 := TensorProduct.tmul ℂ QOne QOne

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
  (IP.f st00 st01 = 0) ∧
  (IP.f st00 st10 = 0) ∧
  (IP.f st00 st11 = 0) ∧
  (IP.f st01 st00 = 0) ∧
  (IP.f st01 st10 = 0) ∧
  (IP.f st01 st11 = 0) ∧
  (IP.f st10 st01 = 0) ∧
  (IP.f st10 st00 = 0) ∧
  (IP.f st10 st11 = 0) ∧
  (IP.f st11 st01 = 0) ∧
  (IP.f st11 st10 = 0) ∧
  (IP.f st11 st00 = 0) := by
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
  all_goals simp [st00, st01, st10, st11]
  all_goals simp [IP.f, IP.IPLeft, IP.IPRight]
  all_goals try po
  all_goals simp [IP.f, QZero, QOne]

theorem test2:
  (IP.f st00 st00 = 1) ∧
  (IP.f st01 st01 = 1) ∧
  (IP.f st10 st10 = 1) ∧
  (IP.f st11 st11 = 1) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [st00, st01, st10, st11]
  all_goals simp [IP.f, IP.IPLeft, IP.IPRight]
  all_goals simp [QZero, QOne]
