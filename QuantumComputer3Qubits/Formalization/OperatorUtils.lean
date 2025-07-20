import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.Decompose
import QuantumComputer3Qubits.Formalization.Operators
-- This file contains utility definitions/functions for
-- operators.

-- OU means "Operator Utils"
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

-- This lemma allows to prove equality of two StateReg3
-- instances by proving that their inner products with a
-- predefined set of StateReg3 instances are equals.
-- This lemma allows to reduce the problem of proving
-- equality of StateReg3 to the problem of proving
-- equality of complex numbers.
lemma Equality3S(s1 s2: StateReg3):
(∀ v1 v2 v3: CS.CV, (IP.f s1 (CS.qqq v1 v2 v3) = IP.f s2 (CS.qqq v1 v2 v3))) →
s1 = s2 := by
  let eq := EqStatesByIP
  simp [CS.qqq] at eq

  let ⟨c1, st_1⟩ := DC.dsReg3.prop s1
  let ⟨c2, st_2⟩ := DC.dsReg3.prop s2
  simp [FS.FS8, DC.dsReg3, DC.tp_4_2, DC.tp_2_2, DC.dc0, DC.dc1, DC.dc2] at st_1 st_2
  intro h
  simp [st_1, st_2, FS.FS8] at h

  let h000 := h 0 0 0
  simp [IP.distrLeft, IP.distrRight, IP.smulLeft, eq] at h000
  rw [ComplexUtil.Aux] at h000
  rw [ComplexUtil.Aux] at h000
  let h000_ := ComplexUtil.EqStar (star (c1 0)) (star (c2 0)) h000
  simp [ComplexUtil.DoubleStar] at h000_
  clear h000
  let h000 := h000_

  let h001 := h 0 0 1
  simp [IP.distrLeft, IP.distrRight, IP.smulLeft, eq] at h001
  rw [ComplexUtil.Aux] at h001
  rw [ComplexUtil.Aux] at h001
  let h001_ := ComplexUtil.EqStar (star (c1 1)) (star (c2 1)) h001
  simp [ComplexUtil.DoubleStar] at h001_
  clear h001
  let h001 := h001_

  let h010 := h 0 1 0
  simp [IP.distrLeft, IP.distrRight, IP.smulLeft, eq] at h010
  rw [ComplexUtil.Aux] at h010
  rw [ComplexUtil.Aux] at h010
  let h010_ := ComplexUtil.EqStar (star (c1 2)) (star (c2 2)) h010
  simp [ComplexUtil.DoubleStar] at h010_
  clear h010
  let h010 := h010_

  let h011 := h 0 1 1
  simp [IP.distrLeft, IP.distrRight, IP.smulLeft, eq] at h011
  rw [ComplexUtil.Aux] at h011
  rw [ComplexUtil.Aux] at h011
  let h011_ := ComplexUtil.EqStar (star (c1 3)) (star (c2 3)) h011
  simp [ComplexUtil.DoubleStar] at h011_
  clear h011
  let h011 := h011_

  let h100 := h 1 0 0
  simp [IP.distrLeft, IP.distrRight, IP.smulLeft, eq] at h100
  rw [ComplexUtil.Aux] at h100
  rw [ComplexUtil.Aux] at h100
  let h100_ := ComplexUtil.EqStar (star (c1 4)) (star (c2 4)) h100
  simp [ComplexUtil.DoubleStar] at h100_
  clear h100
  let h100 := h100_

  let h101 := h 1 0 1
  simp [IP.distrLeft, IP.distrRight, IP.smulLeft, eq] at h101
  rw [ComplexUtil.Aux] at h101
  rw [ComplexUtil.Aux] at h101
  let h101_ := ComplexUtil.EqStar (star (c1 5)) (star (c2 5)) h101
  simp [ComplexUtil.DoubleStar] at h101_
  clear h101
  let h101 := h101_

  let h110 := h 1 1 0
  simp [IP.distrLeft, IP.distrRight, IP.smulLeft, eq] at h110
  rw [ComplexUtil.Aux] at h110
  rw [ComplexUtil.Aux] at h110
  let h110_ := ComplexUtil.EqStar (star (c1 6)) (star (c2 6)) h110
  simp [ComplexUtil.DoubleStar] at h110_
  clear h110
  let h110 := h110_

  let h111 := h 1 1 1
  simp [IP.distrLeft, IP.distrRight, IP.smulLeft, eq] at h111
  rw [ComplexUtil.Aux] at h111
  rw [ComplexUtil.Aux] at h111
  let h111_ := ComplexUtil.EqStar (star (c1 7)) (star (c2 7)) h111
  simp [ComplexUtil.DoubleStar] at h111_
  clear h111
  let h111 := h111_

  rw [st_1, st_2]
  rw [h000, h001, h010, h011, h100, h101, h110, h111]

-- This lemma allows to prove equality of two operators
-- by proving that the equality of StateReg3 instances.
-- This lemma allows to reduce the problem of proving
-- equality of operators to the problem of proving
-- equality of StateReg3 instances.
lemma Equality3(op1 op2: OP.o3):
(∀ v1 v2 v3: CS.CV, (op1 (CS.qqq v1 v2 v3) = op2 (CS.qqq v1 v2 v3))) →
op1 = op2 := by
  intro h
  have t:∀s: StateReg3, op1 s = op2 s := by
    intro s
    let ⟨cX, st_x⟩ := DC.dsReg3.prop s
    simp [FS.FS8, DC.dsReg3, DC.tp_4_2, DC.tp_2_2, DC.dc0, DC.dc1, DC.dc2] at st_x
    simp [st_x]
    simp [CS.qqq] at h
    simp [h]
  aesop

-- This type is a core function used to construct OP.o3.
-- The idea is the following:
-- 1) Core function takes three classical bit states.
--    Together they form a classical 3-bit registry state.
-- 2) Each classical 3-bit registry state has analogue
--    3-qubit registry state. So core function is a function
--    from 3-qubit registry state to 3-qubit registry state
--    defined on "classical" states only.
-- 3) We use core function to "lift" it to all states. More
--    formally we generate linear map for all states basing
--    on function for "classical" states only.
--
-- The purpose of this concept is to enable us to define
-- linear operator in a simplified way, - by just defining
-- its values for "classical" states only.
def Core:Type := CS.CV → CS.CV → CS.CV → StateReg3

-- This function generates operator by core function.
noncomputable
def o3ByCore(core: Core): OP.o3 := FS.fs
(fun i: Fin 8 => match i with
| 0 => OP (core 0 0 0) (CS.qqq 0 0 0)
| 1 => OP (core 0 0 1) (CS.qqq 0 0 1)
| 2 => OP (core 0 1 0) (CS.qqq 0 1 0)
| 3 => OP (core 0 1 1) (CS.qqq 0 1 1)
| 4 => OP (core 1 0 0) (CS.qqq 1 0 0)
| 5 => OP (core 1 0 1) (CS.qqq 1 0 1)
| 6 => OP (core 1 1 0) (CS.qqq 1 1 0)
| 7 => OP (core 1 1 1) (CS.qqq 1 1 1)
)

-- This theorem states that we generate linear operator by
-- core function correctly: linear operator values for
-- "classical" states are the same as core function values.
theorem o3CoreCorrect:
∀c: Core, ∀cv1 cv2 cv3: CS.CV,
(o3ByCore c) (CS.qqq cv1 cv2 cv3) = c cv1 cv2 cv3 := by
  let eq := EqStatesByIP
  simp [CS.qqq] at eq

  intro c
  intro cv1 cv2 cv3
  simp [o3ByCore, OP]
  simp [FS.FS8]
  rw [eq]
  rw [eq]
  rw [eq]
  rw [eq]
  rw [eq]
  rw [eq]
  rw [eq]
  rw [eq]
  all_goals fin_cases cv1
  all_goals fin_cases cv2
  all_goals fin_cases cv3
  all_goals simp

-- This function generates adjoint operator by core function.
-- We already have a function generating adjoint operator.
-- Here are differences between these two functions:
-- 1) General function is applicable to any operator while
--    this is applicable only if operator is defined by
--    core function.
-- 2) General function uses orthonormal basis while this
--    uses only outer product. So adjoint generated by
--    by this function is simpler and so easier to work
--    with.
noncomputable
def o3AdjByCore(core: Core): OP.o3 := FS.fs
(fun i: Fin 8 => match i with
| 0 => OP (CS.qqq 0 0 0) (core 0 0 0)
| 1 => OP (CS.qqq 0 0 1) (core 0 0 1)
| 2 => OP (CS.qqq 0 1 0) (core 0 1 0)
| 3 => OP (CS.qqq 0 1 1) (core 0 1 1)
| 4 => OP (CS.qqq 1 0 0) (core 1 0 0)
| 5 => OP (CS.qqq 1 0 1) (core 1 0 1)
| 6 => OP (CS.qqq 1 1 0) (core 1 1 0)
| 7 => OP (CS.qqq 1 1 1) (core 1 1 1)
)

-- This theorem states that the adjoin operator generated
-- above is correct.
theorem o3CoreAdj: ∀c: Core, HC.adj (o3ByCore c) = o3AdjByCore c := by
  intro c
  let ⟨A,prEx,prEq⟩ := HC.adjEx! (o3ByCore c)
  simp at prEx prEq
  have eq1: HC.adj (o3ByCore c) = A := by
    apply prEq (HC.adj (o3ByCore c))
    apply HC.reallyAdj
  have eq2: o3AdjByCore c = A := by
    apply prEq (o3AdjByCore c)
    simp [o3AdjByCore, o3ByCore, FS.FS8]
    apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjOP
  clear prEx prEq
  aesop
