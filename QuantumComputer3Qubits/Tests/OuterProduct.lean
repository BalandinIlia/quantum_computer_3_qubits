import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.ClassicalStates

namespace Test_OuterProduct

theorem test1:
(OP CS.s00 CS.s00 CS.s00 = CS.s00) ∧
(OP CS.s00 CS.s00 CS.s01 = 0) ∧
(OP CS.s00 CS.s00 CS.s10 = 0) ∧
(OP CS.s00 CS.s00 CS.s11 = 0) ∧
(OP CS.s01 CS.s01 CS.s00 = 0) ∧
(OP CS.s01 CS.s01 CS.s01 = CS.s01) ∧
(OP CS.s01 CS.s01 CS.s10 = 0) ∧
(OP CS.s01 CS.s01 CS.s11 = 0) ∧
(OP CS.s10 CS.s10 CS.s00 = 0) ∧
(OP CS.s10 CS.s10 CS.s01 = 0) ∧
(OP CS.s10 CS.s10 CS.s10 = CS.s10) ∧
(OP CS.s10 CS.s10 CS.s11 = 0) ∧
(OP CS.s11 CS.s11 CS.s00 = 0) ∧
(OP CS.s11 CS.s11 CS.s01 = 0) ∧
(OP CS.s11 CS.s11 CS.s10 = 0) ∧
(OP CS.s11 CS.s11 CS.s11 = CS.s11) := by
  simp [OP, IP.f, IP.IPLeft, IP.IPRight, IP.Transfer.lE, isoQubitIndQubitBase]
