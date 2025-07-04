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
