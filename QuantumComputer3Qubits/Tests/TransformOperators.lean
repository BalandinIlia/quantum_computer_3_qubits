import QuantumComputer3Qubits.Formalization.TransformOperators
import QuantumComputer3Qubits.Tests.StateExamples

namespace Test_TransformOperators

def id:OP.o1:=
{
  toFun(s: StateReg1) := s
  map_add' := by aesop
  map_smul' := by aesop
}

theorem idProp: ∀s: StateReg1, id s = s := by
  simp [id]

def not:OP.o1:=
{
  toFun(s: StateReg1) := fun x:Fin 2 =>
        match x with
        | 0 => s 1
        | 1 => s 0
  map_add' := by aesop
  map_smul' := by aesop
}

theorem notProp: (not SE.s0 = SE.s1) ∧ (not SE.s1 = SE.s0) := by
  simp [not]
  aesop

theorem test1:∀i: Fin 3, ∀s: StateReg1Ind i,
              TO.o1_oi1 i id s = s := by
  simp [TO.o1_oi1, LER.reg1i_reg1]
  aesop

theorem test2:∀i: Fin 3,
              (TO.o1_oi1 i not (SE.si0 i) = (SE.si1 i)) ∧
              (TO.o1_oi1 i not (SE.si1 i) = (SE.si0 i)) := by
  simp [TO.o1_oi1, LER.reg1i_reg1]
  aesop

noncomputable
def notIdInd(i1 i2: Fin 3)(ord: i1 < i2):OP.oi2 i1 i2 ord := TO.tpo1o1i i1 i2 ord (TO.o1_oi1 i1 not) (TO.o1_oi1 i2 id)
noncomputable
def notInd(i: Fin 3):OP.oi1 i := TO.o1_oi1 i not

theorem test3:
(TO.tpo2o1i 0 1 (by aesop) 2 (by aesop) (by aesop) (notIdInd 0 1 (by aesop)) (notInd 2) SE.s000 = SE.s101) ∧
(TO.tpo2o1i 0 1 (by aesop) 2 (by aesop) (by aesop) (notIdInd 0 1 (by aesop)) (notInd 2) SE.s010 = SE.s111) ∧
(TO.tpo2o1i 0 1 (by aesop) 2 (by aesop) (by aesop) (notIdInd 0 1 (by aesop)) (notInd 2) SE.s101 = SE.s000) ∧
(TO.tpo2o1i 0 1 (by aesop) 2 (by aesop) (by aesop) (notIdInd 0 1 (by aesop)) (notInd 2) SE.s111 = SE.s010) ∧

(TO.tpo2o1i 0 2 (by aesop) 1 (by aesop) (by aesop) (notIdInd 0 2 (by aesop)) (notInd 1) SE.s000 = SE.s110) ∧
(TO.tpo2o1i 0 2 (by aesop) 1 (by aesop) (by aesop) (notIdInd 0 2 (by aesop)) (notInd 1) SE.s010 = SE.s100) ∧
(TO.tpo2o1i 0 2 (by aesop) 1 (by aesop) (by aesop) (notIdInd 0 2 (by aesop)) (notInd 1) SE.s011 = SE.s101) ∧
(TO.tpo2o1i 0 2 (by aesop) 1 (by aesop) (by aesop) (notIdInd 0 2 (by aesop)) (notInd 1) SE.s111 = SE.s001) ∧

(TO.tpo2o1i 1 2 (by aesop) 0 (by aesop) (by aesop) (notIdInd 1 2 (by aesop)) (notInd 0) SE.s000 = SE.s110) ∧
(TO.tpo2o1i 1 2 (by aesop) 0 (by aesop) (by aesop) (notIdInd 1 2 (by aesop)) (notInd 0) SE.s010 = SE.s100) ∧
(TO.tpo2o1i 1 2 (by aesop) 0 (by aesop) (by aesop) (notIdInd 1 2 (by aesop)) (notInd 0) SE.s011 = SE.s101) ∧
(TO.tpo2o1i 1 2 (by aesop) 0 (by aesop) (by aesop) (notIdInd 1 2 (by aesop)) (notInd 0) SE.s111 = SE.s001) := by
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals try apply And.intro
  all_goals simp [TO.tpo2o1i, notIdInd, TO.tpo1o1i, TO.o1_oi1, TO.impl, LER.reg2ireg1i_reg3, LER.reg1i_reg1, notInd, not]
  all_goals aesop
