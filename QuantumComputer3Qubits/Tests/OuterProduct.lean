import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.ClassicalStates

namespace Test_OuterProduct

theorem test1:
(OP SE.s00 SE.s00 SE.s00 = SE.s00) ∧
(OP SE.s00 SE.s00 SE.s01 = 0) ∧
(OP SE.s00 SE.s00 SE.s10 = 0) ∧
(OP SE.s00 SE.s00 SE.s11 = 0) ∧
(OP SE.s01 SE.s01 SE.s00 = 0) ∧
(OP SE.s01 SE.s01 SE.s01 = SE.s01) ∧
(OP SE.s01 SE.s01 SE.s10 = 0) ∧
(OP SE.s01 SE.s01 SE.s11 = 0) ∧
(OP SE.s10 SE.s10 SE.s00 = 0) ∧
(OP SE.s10 SE.s10 SE.s01 = 0) ∧
(OP SE.s10 SE.s10 SE.s10 = SE.s10) ∧
(OP SE.s10 SE.s10 SE.s11 = 0) ∧
(OP SE.s11 SE.s11 SE.s00 = 0) ∧
(OP SE.s11 SE.s11 SE.s01 = 0) ∧
(OP SE.s11 SE.s11 SE.s10 = 0) ∧
(OP SE.s11 SE.s11 SE.s11 = SE.s11) := by
  simp [OP, IP.f, IP.IPLeft, IP.IPRight, IP.Transfer.lE, isoQubitIndQubitBase]
