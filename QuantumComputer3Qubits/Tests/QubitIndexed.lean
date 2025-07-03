import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.QubitIndexed

namespace Test

-- check that module can be synthesized for each indexed qubit
#synth Module ℂ (QubitInd 0)
#synth Module ℂ (QubitInd 1)
#synth Module ℂ (QubitInd 2)

--
noncomputable
def QZeroImage(i: Fin 3) := LinearEquiv.symm (isoQubitIndQubitBase i) QZero

noncomputable
def QOneImage(i: Fin 3) := LinearEquiv.symm (isoQubitIndQubitBase i) QOne

-- check that image of QZero behaves as expected
theorem testQZeroImage:
  (QZeroImage 0 X1.a = 1) ∧
  (QZeroImage 0 X1.b = 0) ∧
  (QZeroImage 1 X2.a = 1) ∧
  (QZeroImage 1 X2.b = 0) ∧
  (QZeroImage 2 X3.a = 1) ∧
  (QZeroImage 2 X3.b = 0) := by
  simp [QZeroImage, isoQubitIndQubitBase, QZero]

-- check that image of QOne behaves as expected
theorem testQOneImage:
  (QOneImage 0 X1.a = 0) ∧
  (QOneImage 0 X1.b = 1) ∧
  (QOneImage 1 X2.a = 0) ∧
  (QOneImage 1 X2.b = 1) ∧
  (QOneImage 2 X3.a = 0) ∧
  (QOneImage 2 X3.b = 1) := by
  simp [QOneImage, isoQubitIndQubitBase, QOne]

-- check that inner product is defined for indexed qubits
#synth IP (QubitInd 0)
#synth IP (QubitInd 1)
#synth IP (QubitInd 2)
