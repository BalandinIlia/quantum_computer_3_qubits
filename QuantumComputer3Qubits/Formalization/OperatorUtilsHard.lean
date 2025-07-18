import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.Decompose
-- This file contains operator "hard" utilities which require much
-- Lean workload for proof.
-- These utilities were moved to a separate (from other
-- utilities) file for convinence: when we change utilities
-- file we don't have to wait until these utilities compile.

-- OU means "operator utils"
namespace OU

theorem EqStatesByIP:
  ∀cv1 cv1_ cv2 cv2_ cv3 cv3_: CS.CV,
      IP.f (CS.qqq cv1 cv2 cv3)
           (CS.qqq cv1_ cv2_ cv3_) =
      if (cv1 = cv1_ ∧ cv2 = cv2_ ∧ cv3 = cv3_)
          then 1
          else 0 := by
  intro cv1 cv1_ cv2 cv2_ cv3 cv3_
  simp [IP.f, IP.IPLeft, IP.IPRight, IP.Transfer.lE]

  generalize r0:(isoQubitIndQubitBase 0) (CS.qi cv1 0) 0 = co0
  generalize r1:(isoQubitIndQubitBase 0) (CS.qi cv1_ 0) 0 = co1
  generalize r2:(isoQubitIndQubitBase 0) (CS.qi cv1 0) 1 = co2
  generalize r3:(isoQubitIndQubitBase 0) (CS.qi cv1_ 0) 1 = co3
  generalize r4:(isoQubitIndQubitBase 1) (CS.qi cv2 1) 0 = co4
  generalize r5:(isoQubitIndQubitBase 1) (CS.qi cv2_ 1) 0 = co5
  generalize r6:(isoQubitIndQubitBase 1) (CS.qi cv2 1) 1 = co6
  generalize r7:(isoQubitIndQubitBase 1) (CS.qi cv2_ 1) 1 = co7
  generalize r8:(isoQubitIndQubitBase 2) (CS.qi cv3 2) 0 = co8
  generalize r9:(isoQubitIndQubitBase 2) (CS.qi cv3_ 2) 0 = co9
  generalize r10:(isoQubitIndQubitBase 2) (CS.qi cv3 2) 1 = co10
  generalize r11:(isoQubitIndQubitBase 2) (CS.qi cv3_ 2) 1 = co11

  have l0: co0 = if cv1 = 0 then 1 else 0 := by
    rw [Eq.symm r0]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv1
    all_goals simp
  have l1: co1 = if cv1_ = 0 then 1 else 0 := by
    rw [Eq.symm r1]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv1_
    all_goals simp
  have l2: co2 = if cv1 = 0 then 0 else 1 := by
    rw [Eq.symm r2]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv1
    all_goals simp
  have l3: co3 = if cv1_ = 0 then 0 else 1 := by
    rw [Eq.symm r3]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv1_
    all_goals simp
  have l4: co4 = if cv2 = 0 then 1 else 0 := by
    rw [Eq.symm r4]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv2
    all_goals simp
  have l5: co5 = if cv2_ = 0 then 1 else 0 := by
    rw [Eq.symm r5]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv2_
    all_goals simp
  have l6: co6 = if cv2 = 0 then 0 else 1 := by
    rw [Eq.symm r6]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv2
    all_goals simp
  have l7: co7 = if cv2_ = 0 then 0 else 1 := by
    rw [Eq.symm r7]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv2_
    all_goals simp
  have l8: co8 = if cv3 = 0 then 1 else 0 := by
    rw [Eq.symm r8]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv3
    all_goals simp
  have l9: co9 = if cv3_ = 0 then 1 else 0 := by
    rw [Eq.symm r9]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv3_
    all_goals simp
  have l10: co10 = if cv3 = 0 then 0 else 1 := by
    rw [Eq.symm r10]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv3
    all_goals simp
  have l11: co11 = if cv3_ = 0 then 0 else 1 := by
    rw [Eq.symm r11]
    simp [isoQubitIndQubitBase, CS.qi]
    fin_cases cv3_
    all_goals simp
  simp [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]
  clear l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
  clear r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  clear co0 co1 co2 co3 co4 co5 co6 co7 co8 co9 co10 co11

  all_goals fin_cases cv1
  all_goals fin_cases cv1_
  all_goals simp
  all_goals fin_cases cv2
  all_goals fin_cases cv2_
  all_goals simp
  all_goals fin_cases cv3
  all_goals fin_cases cv3_
  all_goals simp
