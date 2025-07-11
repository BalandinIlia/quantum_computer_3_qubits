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
import QuantumComputer3Qubits.Tests.StateExamples

namespace Hoare

inductive H where
| cond1{i:Fin 3}:                     (OP.oi1 i) → H
| cond2{i1 i2: Fin 3}{ord: i1 < i2}:  (OP.oi2 i1 i2 ord) → H
| cond3:                              OP.o3 → H

inductive Prog where
| skip:                              Prog
| ass1{i:Fin 3}:                     StateReg1Ind i → Prog
| ass2{i1 i2: Fin 3}{ord: i1 < i2}:  StateReg2Ind i1 i2 ord → Prog
| ass3:                              StateReg3 → Prog
| gate1{i:Fin 3}:                    OP.oi1 i → Prog
| gate2{i1 i2: Fin 3}{o: i1 < i2}:   OP.oi2 i1 i2 o → Prog
| gate3:                             OP.o3 → Prog
| meas1:                             Fin 3 → Prog → Prog → Prog
| seq:                               Prog → Prog → Prog

noncomputable
instance inth(i: Fin 3): OrthonormalBasis (StateReg1Ind i) :=
match i with
| 0 => inferInstance
| 1 => inferInstance
| 2 => inferInstance

noncomputable
instance intth(i1 i2: Fin 3)(ord: i1 < i2): OrthonormalBasis (StateReg2Ind i1 i2 ord) :=
match i1, i2 with
| 0, 0 => inferInstance
| 0, 1 => inferInstance
| 0, 2 => inferInstance
| 1, 0 => inferInstance
| 1, 1 => inferInstance
| 1, 2 => inferInstance
| 2, 0 => inferInstance
| 2, 1 => inferInstance
| 2, 2 => inferInstance

inductive Hoar: H → Prog → H → Prop
| Ax.Sk:   ∀h: H, Hoar h Prog.skip h
| Ax.UTF1(i: Fin 3):
    ∀op tr: (OP.oi1 i),
      Hoar (H.cond1 op)
           (Prog.gate1 tr)
           (H.cond1 ((tr • op)•(HC.adj tr)))
| Ax.UTF2(i1 i2: Fin 3)(ord: i1 < i2):
    ∀op tr: (OP.oi2 i1 i2 ord),
      Hoar (H.cond2 op)
           (Prog.gate2 tr)
           (H.cond2 ((tr • op)•(HC.adj tr)))
| Ax.Inf_1_1(i1 i2: Fin 3)(ord: i1 < i2):
    ∀op: OP.oi1 i1, ∀s: StateReg1Ind i2,
      Hoar (H.cond1 op)
           (Prog.ass1 s)
           (H.cond2 (TO.tpo1o1i i1 i2 ord op (OP s s)))
| Ax.Inf_1_1_(i1 i2: Fin 3)(ord: i1 > i2):
    ∀op: OP.oi1 i1, ∀s: StateReg1Ind i2,
      Hoar (H.cond1 op)
           (Prog.ass1 s)
           (H.cond2 (TO.tpo1o1i i2 i1 ord (OP s s) op))
| Ax.Inf_2_1(i1 i2: Fin 3)(ord: i1 < i2)(i3: Fin 3)(neq1: ¬(i1=i3))(neq2: ¬(i2=i3)):
    ∀op: OP.oi2 i1 i2 ord, ∀s: StateReg1Ind i3,
      Hoar (H.cond2 op)
           (Prog.ass1 s)
           (H.cond3 (TO.tpo2o1i i1 i2 ord i3 (by aesop) (by aesop) op (OP s s)))
| Ax.Inf_1_2(i1 i2: Fin 3)(ord: i1 < i2)(i3: Fin 3)(neq1: ¬(i1=i3))(neq2: ¬(i2=i3)):
    ∀op: OP.oi1 i3, ∀s: StateReg2Ind i1 i2 ord,
      Hoar (H.cond1 op)
           (Prog.ass2 s)
           (H.cond3 (TO.tpo2o1i i1 i2 ord i3 (by aesop) (by aesop) (OP s s) op))
| R.SC: ∀A B C: H, ∀S1 S2: Prog, Hoar A S1 B → Hoar B S2 C → Hoar A (Prog.seq S1 S2) C

noncomputable
def one:StateReg1Ind 2 := SE.si1 2

set_option maxHeartbeats 1000000

theorem th1:
Hoar (H.cond2 (OP (SE.si00 0 1 (by aesop)) (SE.si00 0 1 (by aesop))))
     (Prog.ass1 one)
     (H.cond3 (OP SE.s001 SE.s001)) := by
  let st := Hoar.Ax.Inf_2_1 0 1 (by aesop) 2 (by aesop) (by aesop) (OP (SE.si00 0 1 (by aesop)) (SE.si00 0 1 (by aesop))) one
  have repr:
    (((TO.tpo2o1i 0 1 (by aesop) 2 (by aesop) (by aesop)) (OP (SE.si00 0 1 (by aesop)) (SE.si00 0 1 (by aesop)))) (OP one one)) =
    (OP SE.s001 SE.s001) := by
    clear st
    simp only [one]
    let sta:= LER.reg2ireg1i_reg3 0 1 (by aesop) 2 (by aesop) (by aesop) (TensorProduct.tmul ℂ (SE.si00 0 1 (by aesop)) (SE.si1 2))
    have t1: ((TO.tpo2o1i 0 1 (by aesop) 2 (by aesop) (by aesop)) (OP (SE.si00 0 1 (by aesop)) (SE.si00 0 1 (by aesop)))) (OP (SE.si1 2) (SE.si1 2)) = OP sta sta := by
      simp only [sta]
      clear sta
      apply OP.hjk
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      {
        generalize r000:((isoQubitIndQubitBase 0) (SE.si0 0) 0) = co000
        generalize r100:((isoQubitIndQubitBase 1) (SE.si0 1) 0) = co100
        generalize r200:((isoQubitIndQubitBase 2) (SE.si0 2) 0) = co200
        generalize r010:((isoQubitIndQubitBase 0) (SE.si1 0) 0) = co010
        generalize r110:((isoQubitIndQubitBase 1) (SE.si1 1) 0) = co110
        generalize r210:((isoQubitIndQubitBase 2) (SE.si1 2) 0) = co210
        generalize r001:((isoQubitIndQubitBase 0) (SE.si0 0) 1) = co001
        generalize r101:((isoQubitIndQubitBase 1) (SE.si0 1) 1) = co101
        generalize r201:((isoQubitIndQubitBase 2) (SE.si0 2) 1) = co201
        generalize r011:((isoQubitIndQubitBase 0) (SE.si1 0) 1) = co011
        generalize r111:((isoQubitIndQubitBase 1) (SE.si1 1) 1) = co111
        generalize r211:((isoQubitIndQubitBase 2) (SE.si1 2) 1) = co211
        have s000: co000 = 1 := by simp [Eq.symm r000, SE.si0, isoQubitIndQubitBase]
        have s100: co100 = 1 := by simp [Eq.symm r100, SE.si0, isoQubitIndQubitBase]
        have s200: co200 = 1 := by simp [Eq.symm r200, SE.si0, isoQubitIndQubitBase]
        have s010: co010 = 0 := by simp [Eq.symm r010, SE.si1, isoQubitIndQubitBase]
        have s110: co110 = 0 := by simp [Eq.symm r110, SE.si1, isoQubitIndQubitBase]
        have s210: co210 = 0 := by simp [Eq.symm r210, SE.si1, isoQubitIndQubitBase]
        have s001: co001 = 0 := by simp [Eq.symm r001, SE.si0, isoQubitIndQubitBase]
        have s101: co101 = 0 := by simp [Eq.symm r101, SE.si0, isoQubitIndQubitBase]
        have s201: co201 = 0 := by simp [Eq.symm r201, SE.si0, isoQubitIndQubitBase]
        have s011: co011 = 1 := by simp [Eq.symm r011, SE.si1, isoQubitIndQubitBase]
        have s111: co111 = 1 := by simp [Eq.symm r111, SE.si1, isoQubitIndQubitBase]
        have s211: co211 = 1 := by simp [Eq.symm r211, SE.si1, isoQubitIndQubitBase]
        simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
      }
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      {
        generalize r000:((isoQubitIndQubitBase 0) (SE.si0 0) 0) = co000
        generalize r100:((isoQubitIndQubitBase 1) (SE.si0 1) 0) = co100
        generalize r200:((isoQubitIndQubitBase 2) (SE.si0 2) 0) = co200
        generalize r010:((isoQubitIndQubitBase 0) (SE.si1 0) 0) = co010
        generalize r110:((isoQubitIndQubitBase 1) (SE.si1 1) 0) = co110
        generalize r210:((isoQubitIndQubitBase 2) (SE.si1 2) 0) = co210
        generalize r001:((isoQubitIndQubitBase 0) (SE.si0 0) 1) = co001
        generalize r101:((isoQubitIndQubitBase 1) (SE.si0 1) 1) = co101
        generalize r201:((isoQubitIndQubitBase 2) (SE.si0 2) 1) = co201
        generalize r011:((isoQubitIndQubitBase 0) (SE.si1 0) 1) = co011
        generalize r111:((isoQubitIndQubitBase 1) (SE.si1 1) 1) = co111
        generalize r211:((isoQubitIndQubitBase 2) (SE.si1 2) 1) = co211
        have s000: co000 = 1 := by simp [Eq.symm r000, SE.si0, isoQubitIndQubitBase]
        have s100: co100 = 1 := by simp [Eq.symm r100, SE.si0, isoQubitIndQubitBase]
        have s200: co200 = 1 := by simp [Eq.symm r200, SE.si0, isoQubitIndQubitBase]
        have s010: co010 = 0 := by simp [Eq.symm r010, SE.si1, isoQubitIndQubitBase]
        have s110: co110 = 0 := by simp [Eq.symm r110, SE.si1, isoQubitIndQubitBase]
        have s210: co210 = 0 := by simp [Eq.symm r210, SE.si1, isoQubitIndQubitBase]
        have s001: co001 = 0 := by simp [Eq.symm r001, SE.si0, isoQubitIndQubitBase]
        have s101: co101 = 0 := by simp [Eq.symm r101, SE.si0, isoQubitIndQubitBase]
        have s201: co201 = 0 := by simp [Eq.symm r201, SE.si0, isoQubitIndQubitBase]
        have s011: co011 = 1 := by simp [Eq.symm r011, SE.si1, isoQubitIndQubitBase]
        have s111: co111 = 1 := by simp [Eq.symm r111, SE.si1, isoQubitIndQubitBase]
        have s211: co211 = 1 := by simp [Eq.symm r211, SE.si1, isoQubitIndQubitBase]
        simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
      }
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      {
        generalize r000:((isoQubitIndQubitBase 0) (SE.si0 0) 0) = co000
        generalize r100:((isoQubitIndQubitBase 1) (SE.si0 1) 0) = co100
        generalize r200:((isoQubitIndQubitBase 2) (SE.si0 2) 0) = co200
        generalize r010:((isoQubitIndQubitBase 0) (SE.si1 0) 0) = co010
        generalize r110:((isoQubitIndQubitBase 1) (SE.si1 1) 0) = co110
        generalize r210:((isoQubitIndQubitBase 2) (SE.si1 2) 0) = co210
        generalize r001:((isoQubitIndQubitBase 0) (SE.si0 0) 1) = co001
        generalize r101:((isoQubitIndQubitBase 1) (SE.si0 1) 1) = co101
        generalize r201:((isoQubitIndQubitBase 2) (SE.si0 2) 1) = co201
        generalize r011:((isoQubitIndQubitBase 0) (SE.si1 0) 1) = co011
        generalize r111:((isoQubitIndQubitBase 1) (SE.si1 1) 1) = co111
        generalize r211:((isoQubitIndQubitBase 2) (SE.si1 2) 1) = co211
        have s000: co000 = 1 := by simp [Eq.symm r000, SE.si0, isoQubitIndQubitBase]
        have s100: co100 = 1 := by simp [Eq.symm r100, SE.si0, isoQubitIndQubitBase]
        have s200: co200 = 1 := by simp [Eq.symm r200, SE.si0, isoQubitIndQubitBase]
        have s010: co010 = 0 := by simp [Eq.symm r010, SE.si1, isoQubitIndQubitBase]
        have s110: co110 = 0 := by simp [Eq.symm r110, SE.si1, isoQubitIndQubitBase]
        have s210: co210 = 0 := by simp [Eq.symm r210, SE.si1, isoQubitIndQubitBase]
        have s001: co001 = 0 := by simp [Eq.symm r001, SE.si0, isoQubitIndQubitBase]
        have s101: co101 = 0 := by simp [Eq.symm r101, SE.si0, isoQubitIndQubitBase]
        have s201: co201 = 0 := by simp [Eq.symm r201, SE.si0, isoQubitIndQubitBase]
        have s011: co011 = 1 := by simp [Eq.symm r011, SE.si1, isoQubitIndQubitBase]
        have s111: co111 = 1 := by simp [Eq.symm r111, SE.si1, isoQubitIndQubitBase]
        have s211: co211 = 1 := by simp [Eq.symm r211, SE.si1, isoQubitIndQubitBase]
        simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
      }
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      {
        generalize r000:((isoQubitIndQubitBase 0) (SE.si0 0) 0) = co000
        generalize r100:((isoQubitIndQubitBase 1) (SE.si0 1) 0) = co100
        generalize r200:((isoQubitIndQubitBase 2) (SE.si0 2) 0) = co200
        generalize r010:((isoQubitIndQubitBase 0) (SE.si1 0) 0) = co010
        generalize r110:((isoQubitIndQubitBase 1) (SE.si1 1) 0) = co110
        generalize r210:((isoQubitIndQubitBase 2) (SE.si1 2) 0) = co210
        generalize r001:((isoQubitIndQubitBase 0) (SE.si0 0) 1) = co001
        generalize r101:((isoQubitIndQubitBase 1) (SE.si0 1) 1) = co101
        generalize r201:((isoQubitIndQubitBase 2) (SE.si0 2) 1) = co201
        generalize r011:((isoQubitIndQubitBase 0) (SE.si1 0) 1) = co011
        generalize r111:((isoQubitIndQubitBase 1) (SE.si1 1) 1) = co111
        generalize r211:((isoQubitIndQubitBase 2) (SE.si1 2) 1) = co211
        have s000: co000 = 1 := by simp [Eq.symm r000, SE.si0, isoQubitIndQubitBase]
        have s100: co100 = 1 := by simp [Eq.symm r100, SE.si0, isoQubitIndQubitBase]
        have s200: co200 = 1 := by simp [Eq.symm r200, SE.si0, isoQubitIndQubitBase]
        have s010: co010 = 0 := by simp [Eq.symm r010, SE.si1, isoQubitIndQubitBase]
        have s110: co110 = 0 := by simp [Eq.symm r110, SE.si1, isoQubitIndQubitBase]
        have s210: co210 = 0 := by simp [Eq.symm r210, SE.si1, isoQubitIndQubitBase]
        have s001: co001 = 0 := by simp [Eq.symm r001, SE.si0, isoQubitIndQubitBase]
        have s101: co101 = 0 := by simp [Eq.symm r101, SE.si0, isoQubitIndQubitBase]
        have s201: co201 = 0 := by simp [Eq.symm r201, SE.si0, isoQubitIndQubitBase]
        have s011: co011 = 1 := by simp [Eq.symm r011, SE.si1, isoQubitIndQubitBase]
        have s111: co111 = 1 := by simp [Eq.symm r111, SE.si1, isoQubitIndQubitBase]
        have s211: co211 = 1 := by simp [Eq.symm r211, SE.si1, isoQubitIndQubitBase]
        simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
      }
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      {
        generalize r000:((isoQubitIndQubitBase 0) (SE.si0 0) 0) = co000
        generalize r100:((isoQubitIndQubitBase 1) (SE.si0 1) 0) = co100
        generalize r200:((isoQubitIndQubitBase 2) (SE.si0 2) 0) = co200
        generalize r010:((isoQubitIndQubitBase 0) (SE.si1 0) 0) = co010
        generalize r110:((isoQubitIndQubitBase 1) (SE.si1 1) 0) = co110
        generalize r210:((isoQubitIndQubitBase 2) (SE.si1 2) 0) = co210
        generalize r001:((isoQubitIndQubitBase 0) (SE.si0 0) 1) = co001
        generalize r101:((isoQubitIndQubitBase 1) (SE.si0 1) 1) = co101
        generalize r201:((isoQubitIndQubitBase 2) (SE.si0 2) 1) = co201
        generalize r011:((isoQubitIndQubitBase 0) (SE.si1 0) 1) = co011
        generalize r111:((isoQubitIndQubitBase 1) (SE.si1 1) 1) = co111
        generalize r211:((isoQubitIndQubitBase 2) (SE.si1 2) 1) = co211
        have s000: co000 = 1 := by simp [Eq.symm r000, SE.si0, isoQubitIndQubitBase]
        have s100: co100 = 1 := by simp [Eq.symm r100, SE.si0, isoQubitIndQubitBase]
        have s200: co200 = 1 := by simp [Eq.symm r200, SE.si0, isoQubitIndQubitBase]
        have s010: co010 = 0 := by simp [Eq.symm r010, SE.si1, isoQubitIndQubitBase]
        have s110: co110 = 0 := by simp [Eq.symm r110, SE.si1, isoQubitIndQubitBase]
        have s210: co210 = 0 := by simp [Eq.symm r210, SE.si1, isoQubitIndQubitBase]
        have s001: co001 = 0 := by simp [Eq.symm r001, SE.si0, isoQubitIndQubitBase]
        have s101: co101 = 0 := by simp [Eq.symm r101, SE.si0, isoQubitIndQubitBase]
        have s201: co201 = 0 := by simp [Eq.symm r201, SE.si0, isoQubitIndQubitBase]
        have s011: co011 = 1 := by simp [Eq.symm r011, SE.si1, isoQubitIndQubitBase]
        have s111: co111 = 1 := by simp [Eq.symm r111, SE.si1, isoQubitIndQubitBase]
        have s211: co211 = 1 := by simp [Eq.symm r211, SE.si1, isoQubitIndQubitBase]
        simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
      }
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      {
        generalize r000:((isoQubitIndQubitBase 0) (SE.si0 0) 0) = co000
        generalize r100:((isoQubitIndQubitBase 1) (SE.si0 1) 0) = co100
        generalize r200:((isoQubitIndQubitBase 2) (SE.si0 2) 0) = co200
        generalize r010:((isoQubitIndQubitBase 0) (SE.si1 0) 0) = co010
        generalize r110:((isoQubitIndQubitBase 1) (SE.si1 1) 0) = co110
        generalize r210:((isoQubitIndQubitBase 2) (SE.si1 2) 0) = co210
        generalize r001:((isoQubitIndQubitBase 0) (SE.si0 0) 1) = co001
        generalize r101:((isoQubitIndQubitBase 1) (SE.si0 1) 1) = co101
        generalize r201:((isoQubitIndQubitBase 2) (SE.si0 2) 1) = co201
        generalize r011:((isoQubitIndQubitBase 0) (SE.si1 0) 1) = co011
        generalize r111:((isoQubitIndQubitBase 1) (SE.si1 1) 1) = co111
        generalize r211:((isoQubitIndQubitBase 2) (SE.si1 2) 1) = co211
        have s000: co000 = 1 := by simp [Eq.symm r000, SE.si0, isoQubitIndQubitBase]
        have s100: co100 = 1 := by simp [Eq.symm r100, SE.si0, isoQubitIndQubitBase]
        have s200: co200 = 1 := by simp [Eq.symm r200, SE.si0, isoQubitIndQubitBase]
        have s010: co010 = 0 := by simp [Eq.symm r010, SE.si1, isoQubitIndQubitBase]
        have s110: co110 = 0 := by simp [Eq.symm r110, SE.si1, isoQubitIndQubitBase]
        have s210: co210 = 0 := by simp [Eq.symm r210, SE.si1, isoQubitIndQubitBase]
        have s001: co001 = 0 := by simp [Eq.symm r001, SE.si0, isoQubitIndQubitBase]
        have s101: co101 = 0 := by simp [Eq.symm r101, SE.si0, isoQubitIndQubitBase]
        have s201: co201 = 0 := by simp [Eq.symm r201, SE.si0, isoQubitIndQubitBase]
        have s011: co011 = 1 := by simp [Eq.symm r011, SE.si1, isoQubitIndQubitBase]
        have s111: co111 = 1 := by simp [Eq.symm r111, SE.si1, isoQubitIndQubitBase]
        have s211: co211 = 1 := by simp [Eq.symm r211, SE.si1, isoQubitIndQubitBase]
        simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
      }
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      {
        generalize r000:((isoQubitIndQubitBase 0) (SE.si0 0) 0) = co000
        generalize r100:((isoQubitIndQubitBase 1) (SE.si0 1) 0) = co100
        generalize r200:((isoQubitIndQubitBase 2) (SE.si0 2) 0) = co200
        generalize r010:((isoQubitIndQubitBase 0) (SE.si1 0) 0) = co010
        generalize r110:((isoQubitIndQubitBase 1) (SE.si1 1) 0) = co110
        generalize r210:((isoQubitIndQubitBase 2) (SE.si1 2) 0) = co210
        generalize r001:((isoQubitIndQubitBase 0) (SE.si0 0) 1) = co001
        generalize r101:((isoQubitIndQubitBase 1) (SE.si0 1) 1) = co101
        generalize r201:((isoQubitIndQubitBase 2) (SE.si0 2) 1) = co201
        generalize r011:((isoQubitIndQubitBase 0) (SE.si1 0) 1) = co011
        generalize r111:((isoQubitIndQubitBase 1) (SE.si1 1) 1) = co111
        generalize r211:((isoQubitIndQubitBase 2) (SE.si1 2) 1) = co211
        have s000: co000 = 1 := by simp [Eq.symm r000, SE.si0, isoQubitIndQubitBase]
        have s100: co100 = 1 := by simp [Eq.symm r100, SE.si0, isoQubitIndQubitBase]
        have s200: co200 = 1 := by simp [Eq.symm r200, SE.si0, isoQubitIndQubitBase]
        have s010: co010 = 0 := by simp [Eq.symm r010, SE.si1, isoQubitIndQubitBase]
        have s110: co110 = 0 := by simp [Eq.symm r110, SE.si1, isoQubitIndQubitBase]
        have s210: co210 = 0 := by simp [Eq.symm r210, SE.si1, isoQubitIndQubitBase]
        have s001: co001 = 0 := by simp [Eq.symm r001, SE.si0, isoQubitIndQubitBase]
        have s101: co101 = 0 := by simp [Eq.symm r101, SE.si0, isoQubitIndQubitBase]
        have s201: co201 = 0 := by simp [Eq.symm r201, SE.si0, isoQubitIndQubitBase]
        have s011: co011 = 1 := by simp [Eq.symm r011, SE.si1, isoQubitIndQubitBase]
        have s111: co111 = 1 := by simp [Eq.symm r111, SE.si1, isoQubitIndQubitBase]
        have s211: co211 = 1 := by simp [Eq.symm r211, SE.si1, isoQubitIndQubitBase]
        simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
      }
      simp [TO.tpo2o1i, TO.impl, OP, IP.f, IP.IPLeft, IP.IPRight, LER.reg2ireg1i_reg3, IP.Transfer.lE]
      {
        generalize r000:((isoQubitIndQubitBase 0) (SE.si0 0) 0) = co000
        generalize r100:((isoQubitIndQubitBase 1) (SE.si0 1) 0) = co100
        generalize r200:((isoQubitIndQubitBase 2) (SE.si0 2) 0) = co200
        generalize r010:((isoQubitIndQubitBase 0) (SE.si1 0) 0) = co010
        generalize r110:((isoQubitIndQubitBase 1) (SE.si1 1) 0) = co110
        generalize r210:((isoQubitIndQubitBase 2) (SE.si1 2) 0) = co210
        generalize r001:((isoQubitIndQubitBase 0) (SE.si0 0) 1) = co001
        generalize r101:((isoQubitIndQubitBase 1) (SE.si0 1) 1) = co101
        generalize r201:((isoQubitIndQubitBase 2) (SE.si0 2) 1) = co201
        generalize r011:((isoQubitIndQubitBase 0) (SE.si1 0) 1) = co011
        generalize r111:((isoQubitIndQubitBase 1) (SE.si1 1) 1) = co111
        generalize r211:((isoQubitIndQubitBase 2) (SE.si1 2) 1) = co211
        have s000: co000 = 1 := by simp [Eq.symm r000, SE.si0, isoQubitIndQubitBase]
        have s100: co100 = 1 := by simp [Eq.symm r100, SE.si0, isoQubitIndQubitBase]
        have s200: co200 = 1 := by simp [Eq.symm r200, SE.si0, isoQubitIndQubitBase]
        have s010: co010 = 0 := by simp [Eq.symm r010, SE.si1, isoQubitIndQubitBase]
        have s110: co110 = 0 := by simp [Eq.symm r110, SE.si1, isoQubitIndQubitBase]
        have s210: co210 = 0 := by simp [Eq.symm r210, SE.si1, isoQubitIndQubitBase]
        have s001: co001 = 0 := by simp [Eq.symm r001, SE.si0, isoQubitIndQubitBase]
        have s101: co101 = 0 := by simp [Eq.symm r101, SE.si0, isoQubitIndQubitBase]
        have s201: co201 = 0 := by simp [Eq.symm r201, SE.si0, isoQubitIndQubitBase]
        have s011: co011 = 1 := by simp [Eq.symm r011, SE.si1, isoQubitIndQubitBase]
        have s111: co111 = 1 := by simp [Eq.symm r111, SE.si1, isoQubitIndQubitBase]
        have s211: co211 = 1 := by simp [Eq.symm r211, SE.si1, isoQubitIndQubitBase]
        simp [s000, s100, s200, s010, s110, s210, s001, s101, s201, s011, s111, s211]
      }
    have t2: sta = SE.s001 := by
      simp only [sta]
      clear t1 sta
      aesop
    aesop
  rw [repr] at st
  apply st
