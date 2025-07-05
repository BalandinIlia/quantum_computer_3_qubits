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
