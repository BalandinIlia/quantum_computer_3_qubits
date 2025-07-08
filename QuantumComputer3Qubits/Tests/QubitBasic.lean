import QuantumComputer3Qubits.Formalization.QubitBasic

namespace Test_QubiBasic

#synth Module ℂ QubitState
#synth OrthonormalBasis QubitState

theorem test1: IP.f QZero QZero = 1 := by
  simp [IP.f, QubitStateInnerProduct, QZero]

theorem test2: IP.f QZero QOne = 0 := by
  simp [IP.f, QubitStateInnerProduct, QZero, QOne]

theorem test3: IP.f QOne QOne = 1 := by
  simp [IP.f, QubitStateInnerProduct, QZero, QOne]
