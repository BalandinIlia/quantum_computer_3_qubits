import QuantumComputer3Qubits.Formalization.QubitBasic

namespace Test

#synth Module ℂ QubitState

theorem test1: IP.f QZero QZero = 1 := by
  simp [IP.f, QubitStateInnerProduct, QZero]

theorem test2: IP.f QZero QOne = 0 := by
  simp [IP.f, QubitStateInnerProduct, QZero, QOne]

theorem test3: IP.f QOne QOne = 1 := by
  simp [IP.f, QubitStateInnerProduct, QZero, QOne]

-- coefficients of QZero representation in basis
noncomputable
def coefZero := Basis.repr QubitBasis QZero

-- coefficients of QOne representation in basis
noncomputable
def coefOne := Basis.repr QubitBasis QOne

theorem test4: (coefZero 0 = 1) ∧ (coefZero 1 = 0) := by
  simp [coefZero, QZero, QubitBasis]

theorem test5: (coefOne 0 = 0) ∧ (coefOne 1 = 1) := by
  simp [coefOne, QOne, QubitBasis]
