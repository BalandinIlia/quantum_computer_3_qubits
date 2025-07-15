import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.Decompose

-- OU means "operator utils"
namespace OU

set_option maxHeartbeats 100000000

theorem EqStatesByIP:
  ∀cv1 cv1_ cv2 cv2_ cv3 cv3_: CS.CV,
      IP.f ((CS.qi cv1 0 ⊗ₜ[ℂ] CS.qi cv2 1) ⊗ₜ[ℂ] CS.qi cv3 2)
           ((CS.qi cv1_ 0 ⊗ₜ[ℂ] CS.qi cv2_ 1) ⊗ₜ[ℂ] CS.qi cv3_ 2) =
      if (cv1 = cv1_ ∧ cv2 = cv2_ ∧ cv3 = cv3_)
          then 1
          else 0 := by
  intro cv1 cv1_ cv2 cv2_ cv3 cv3_
  all_goals fin_cases cv1
  all_goals fin_cases cv2
  all_goals fin_cases cv3
  all_goals fin_cases cv1_
  all_goals fin_cases cv2_
  all_goals fin_cases cv3_
  all_goals simp [IP.f, IP.IPLeft, IP.IPRight, IP.Transfer.lE]
  all_goals {
    generalize r000:((isoQubitIndQubitBase 0) (CS.qi 0 0) 0) = co000
    generalize r100:((isoQubitIndQubitBase 1) (CS.qi 0 1) 0) = co100
    generalize r200:((isoQubitIndQubitBase 2) (CS.qi 0 2) 0) = co200
    generalize r010:((isoQubitIndQubitBase 0) (CS.qi 1 0) 0) = co010
    generalize r110:((isoQubitIndQubitBase 1) (CS.qi 1 1) 0) = co110
    generalize r210:((isoQubitIndQubitBase 2) (CS.qi 1 2) 0) = co210
    generalize r001:((isoQubitIndQubitBase 0) (CS.qi 0 0) 1) = co001
    generalize r101:((isoQubitIndQubitBase 1) (CS.qi 0 1) 1) = co101
    generalize r201:((isoQubitIndQubitBase 2) (CS.qi 0 2) 1) = co201
    generalize r011:((isoQubitIndQubitBase 0) (CS.qi 1 0) 1) = co011
    generalize r111:((isoQubitIndQubitBase 1) (CS.qi 1 1) 1) = co111
    generalize r211:((isoQubitIndQubitBase 2) (CS.qi 1 2) 1) = co211
    have s000: co000 = 1 := by simp [Eq.symm r000, CS.qi, isoQubitIndQubitBase]
    have s100: co100 = 1 := by simp [Eq.symm r100, CS.qi, isoQubitIndQubitBase]
    have s200: co200 = 1 := by simp [Eq.symm r200, CS.qi, isoQubitIndQubitBase]
    have s010: co010 = 0 := by simp [Eq.symm r010, CS.qi, isoQubitIndQubitBase]
    have s110: co110 = 0 := by simp [Eq.symm r110, CS.qi, isoQubitIndQubitBase]
    have s210: co210 = 0 := by simp [Eq.symm r210, CS.qi, isoQubitIndQubitBase]
    have s001: co001 = 0 := by simp [Eq.symm r001, CS.qi, isoQubitIndQubitBase]
    have s101: co101 = 0 := by simp [Eq.symm r101, CS.qi, isoQubitIndQubitBase]
    have s201: co201 = 0 := by simp [Eq.symm r201, CS.qi, isoQubitIndQubitBase]
    have s011: co011 = 1 := by simp [Eq.symm r011, CS.qi, isoQubitIndQubitBase]
    have s111: co111 = 1 := by simp [Eq.symm r111, CS.qi, isoQubitIndQubitBase]
    have s211: co211 = 1 := by simp [Eq.symm r211, CS.qi, isoQubitIndQubitBase]
    simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
  }
