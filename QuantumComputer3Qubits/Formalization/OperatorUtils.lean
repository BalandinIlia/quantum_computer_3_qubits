import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.Decompose
import QuantumComputer3Qubits.Formalization.Operators
import QuantumComputer3Qubits.Formalization.OperatorUtilsHard

-- OU means "Operator Utils"
namespace OU

private lemma Equality3S(s1 s2: StateReg3):
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

def Core:Type := CS.CV → CS.CV → CS.CV → StateReg3

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
