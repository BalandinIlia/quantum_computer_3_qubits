import QuantumComputer3Qubits.Formalization.QubitBasic
import QuantumComputer3Qubits.Formalization.QubitIndexed
import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.Operators
import QuantumComputer3Qubits.Formalization.TransformOperators
import QuantumComputer3Qubits.Formalization.ComplexUtil
import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.LinearEquivRegistryState
import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.QWhile
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.Decompose
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.OperatorUtils
-- In this file we prove some "classic" Hoare triples
-- in order to check that Hoare inference rules are formalized
-- correctly.

namespace HoareTriples1
open QWhile

set_option maxHeartbeats 500000

macro "solve": tactic =>
`(tactic |
(
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
)
)

-- tactic to prove that a state (s) is normal; in other
-- words to prove that ⟨s|s⟩ = 1
macro "prove_norm": tactic =>
`(tactic|
(
  simp [IP.f, IP.IPLeft, IP.IPRight, IP.Transfer.lE]
  solve
)
)

-- This triple means:
-- If:
-- 1. We have a registry where system of 0th and 1st qubtis
--    is in state |00⟩
-- 2. We assign |1⟩ to the second qubit.
-- Then:
--    The registry is in state |001⟩
-- This is obviously true from physical sense of the operation
-- and confirms correctness of our Hoare rules formalization.
theorem triple1:
classicHoare (CondRegistry.c2 (CS.qqi 0 0 0 1 (by aesop)))
               (Prog.ass1 (CS.qi 1 2) (by prove_norm))
               (CondRegistry.c3 CS.s001) := by
  simp [classicHoare, CondSt]
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  {
    let pr := InfRules.Ax.Inf_2_1 0
                                  1
                                  (by aesop)
                                  2
                                  (by aesop)
                                  (by aesop)
                                  (OP (CS.qqi 0 0 0 1 (by aesop)) (CS.qqi 0 0 0 1 (by aesop)))
                                  (CS.qi 1 2)
    have repr:
      (((TO.tpo2o1i 0 1 (by aesop) 2 (by aesop) (by aesop)) (OP (CS.qqi 0 0 0 1 (by aesop)) (CS.qqi 0 0 0 1 (by aesop)))) (OP (CS.qi 1 2) (CS.qi 1 2))) =
      (OP CS.s001 CS.s001) := by
      clear pr
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      apply OU.Equality3
      intro v1 v2 v3
      all_goals fin_cases v1
      all_goals fin_cases v2
      all_goals fin_cases v3
      all_goals simp
      all_goals solve
    rw [repr] at pr
    apply pr
  }

-- This triple means:
-- If:
-- 1. We have a registry where system of 0th and 2nd qubtis
--    is in state |00⟩
-- 2. We assign |1⟩ to the 1st qubit.
-- Then:
--    The registry is in state |010⟩
-- This is obviously true from physical sense of the operation
-- and confirms correctness of our Hoare rules formalization.
theorem triple2:
classicHoare (CondRegistry.c2 (CS.qqi 0 0 0 2 (by aesop)))
               (Prog.ass1 (CS.qi 1 1) (by prove_norm))
               (CondRegistry.c3 CS.s010) := by
  simp [classicHoare, CondSt]
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  {
    let pr := InfRules.Ax.Inf_2_1 0
                                  2
                                  (by aesop)
                                  1
                                  (by aesop)
                                  (by aesop)
                                  (OP (CS.qqi 0 0 0 2 (by aesop)) (CS.qqi 0 0 0 2 (by aesop)))
                                  (CS.qi 1 1)
    have repr:
      (((TO.tpo2o1i 0 2 (by aesop) 1 (by aesop) (by aesop)) (OP (CS.qqi 0 0 0 2 (by aesop)) (CS.qqi 0 0 0 2 (by aesop)))) (OP (CS.qi 1 1) (CS.qi 1 1))) =
      (OP CS.s010 CS.s010) := by
      clear pr
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      apply OU.Equality3
      intro v1 v2 v3
      all_goals fin_cases v1
      all_goals fin_cases v2
      all_goals fin_cases v3
      all_goals simp
      all_goals solve
    rw [repr] at pr
    apply pr
  }

-- This triple means:
-- If:
-- 1. We have a registry where system of 1st and 2nd qubtis
--    is in state |00⟩
-- 2. We assign |1⟩ to the oth qubit.
-- Then:
--    The registry is in state |100⟩
-- This is obviously true from physical sense of the operation
-- and confirms correctness of our Hoare rules formalization.
theorem triple3:
classicHoare (CondRegistry.c2 (CS.qqi 0 0 1 2 (by aesop)))
               (Prog.ass1 (CS.qi 1 0) (by prove_norm))
               (CondRegistry.c3 CS.s100) := by
  simp [classicHoare, CondSt]
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  {
    let pr := InfRules.Ax.Inf_2_1 1
                                  2
                                  (by aesop)
                                  0
                                  (by aesop)
                                  (by aesop)
                                  (OP (CS.qqi 0 0 1 2 (by aesop)) (CS.qqi 0 0 1 2 (by aesop)))
                                  (CS.qi 1 0)
    have repr:
      (((TO.tpo2o1i 1 2 (by aesop) 0 (by aesop) (by aesop)) (OP (CS.qqi 0 0 1 2 (by aesop)) (CS.qqi 0 0 1 2 (by aesop)))) (OP (CS.qi 1 0) (CS.qi 1 0))) =
      (OP CS.s100 CS.s100) := by
      clear pr
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      apply OU.Equality3
      intro v1 v2 v3
      all_goals fin_cases v1
      all_goals fin_cases v2
      all_goals fin_cases v3
      all_goals simp
      all_goals solve
    rw [repr] at pr
    apply pr
  }

-- This triple means:
-- If:
-- 1. We have a registry where 0th qubit is in state |0⟩
-- 2. We assign |11⟩ to the system of 1st and 2nd qubits.
-- Then:
--    The registry is in state |011⟩
-- This is obviously true from physical sense of the operation
-- and confirms correctness of our Hoare rules formalization.
theorem triple4:
classicHoare (CondRegistry.c1 (CS.qi 0 0))
               (Prog.ass2 (CS.qqi 1 1 1 2 (by aesop)) (by prove_norm))
               (CondRegistry.c3 CS.s011) := by
  simp [classicHoare, CondSt]
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  {
    let pr := InfRules.Ax.Inf_1_2 0
                                  1
                                  2
                                  (by aesop)
                                  (by aesop)
                                  (by aesop)
                                  (OP (CS.qi 0 0) (CS.qi 0 0))
                                  (CS.qqi 1 1 1 2 (by aesop))
    have repr:
      (((TO.tpo2o1i 1 2 (by aesop) 0 (by aesop) (by aesop)) (OP (CS.qqi 1 1 1 2 (by aesop)) (CS.qqi 1 1 1 2 (by aesop)))) (OP (CS.qi 0 0) (CS.qi 0 0))) =
      (OP CS.s011 CS.s011) := by
      clear pr
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      apply OU.Equality3
      intro v1 v2 v3
      all_goals fin_cases v1
      all_goals fin_cases v2
      all_goals fin_cases v3
      all_goals simp
      all_goals solve
    rw [repr] at pr
    apply pr
  }

-- This triple means:
-- If:
-- 1. We have a registry where 1st qubit is in state |0⟩
-- 2. We assign |11⟩ to the system of 0th and 2nd qubits.
-- Then:
--    The registry is in state |101⟩
-- This is obviously true from physical sense of the operation
-- and confirms correctness of our Hoare rules formalization.
theorem triple5:
classicHoare (CondRegistry.c1 (CS.qi 0 1))
               (Prog.ass2 (CS.qqi 1 1 0 2 (by aesop)) (by prove_norm))
               (CondRegistry.c3 CS.s101) := by
  simp [classicHoare, CondSt]
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  {
    let pr := InfRules.Ax.Inf_1_2 1
                                  0
                                  2
                                  (by aesop)
                                  (by aesop)
                                  (by aesop)
                                  (OP (CS.qi 0 1) (CS.qi 0 1))
                                  (CS.qqi 1 1 0 2 (by aesop))
    have repr:
      (((TO.tpo2o1i 0 2 (by aesop) 1 (by aesop) (by aesop)) (OP (CS.qqi 1 1 0 2 (by aesop)) (CS.qqi 1 1 0 2 (by aesop)))) (OP (CS.qi 0 1) (CS.qi 0 1))) =
      (OP CS.s101 CS.s101) := by
      clear pr
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      apply OU.Equality3
      intro v1 v2 v3
      all_goals fin_cases v1
      all_goals fin_cases v2
      all_goals fin_cases v3
      all_goals simp
      all_goals solve
    rw [repr] at pr
    apply pr
  }

-- This triple means:
-- If:
-- 1. We have a registry where 0th qubit is in state |0⟩
-- 2. We assign |1⟩ to the system of 2nd qubits.
-- Then:
--    The system of 0th and second qubit is in state |01⟩
-- This is obviously true from physical sense of the operation
-- and confirms correctness of our Hoare rules formalization.
theorem triple6:
classicHoare (CondRegistry.c1 (CS.qi 0 0))
               (Prog.ass1 (CS.qi 1 2) (by prove_norm))
               (CondRegistry.c2 (CS.qqi 0 1 0 2 (by aesop))) := by
  simp [classicHoare, CondSt]
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  apply And.intro
  {
    simp [IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
    solve
  }
  {
    let pr := InfRules.Ax.Inf_1_1 0
                                  2
                                  (by aesop)
                                  (OP (CS.qi 0 0) (CS.qi 0 0))
                                  (CS.qi 1 2)
                                  (by prove_norm)
    simp at pr
    have repr:
      (((TO.tpo1o1i 0 2 (by aesop)) (OP (CS.qi 0 0) (CS.qi 0 0))) (OP (CS.qi 1 2) (CS.qi 1 2))) =
      (OP (CS.qi 0 0 ⊗ₜ[ℂ] CS.qi 1 2) (CS.qi 0 0 ⊗ₜ[ℂ] CS.qi 1 2)) := by
      clear pr
      rw [TO.tpo1o1i]
      ext q1 q2
      simp
      simp [OP]
      simp [IP.tensorProductIP, IP.IPLeft, IP.IPRight]
      generalize r1: IP.f (CS.qi 0 0) q1 = c1
      generalize r2: IP.f (CS.qi 1 2) q2 = c2
      generalize r3: CS.qi 0 0 = v3
      generalize r4: CS.qi 1 2 = v4
      clear r1 r2 r3 r4 q1 q2
      rw [TensorProduct.smul_tmul]
      rw [TensorProduct.tmul_smul]
      module
    rw [repr] at pr
    apply pr
  }

#print axioms triple1
#print axioms triple2
#print axioms triple3
#print axioms triple4
#print axioms triple5
#print axioms triple6
