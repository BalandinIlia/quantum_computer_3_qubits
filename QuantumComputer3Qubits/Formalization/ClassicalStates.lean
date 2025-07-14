import QuantumComputer3Qubits.Formalization.RegistryState
-- This file formalizes quantum (sub)registry states that are
-- analogs of classical states.
--
-- The key idea is the following: classical bit has two
-- possible states: 0 and 1. Quantum bit state can be
-- represented as a vector in linear space with two basic
-- vectors: |0⟩ and |1⟩. So arbitrary quantum state is
-- α•|0⟩ + β•|1⟩, α,β ∈ ℂ. |0⟩ and |1⟩ can be seen as analogs
-- of classical bit states 0 and 1.
--
-- Furthermore, if we take two bits their possible states are
-- 00, 01, 10, 11. For two qubits analogus states are
-- |0⟩⊗|0⟩, |0⟩⊗|1⟩, |1⟩⊗|0⟩, |1⟩⊗|1⟩.

-- CS means "Classical States"
namespace CS

@[reducible]
-- CV means "classical value", - value that can be assigned
-- to a classical bit
def CV: Type := Fin 2

@[simp]
-- q means "qubit", val is classical bit value
def q(val: CV): StateReg1 :=
match val with
-- analog of state of classical bit with value 0
| 0 => fun x:Fin 2 => match x with
                      | 0 => 1
                      | 1 => 0
-- analog of state of classical bit with value 1
| 1 => fun x:Fin 2 => match x with
                      | 0 => 0
                      | 1 => 1

-- check that q behaves as expected
lemma test1: (q 0 0 = 1) ∧
             (q 0 1 = 0) ∧
             (q 1 0 = 0) ∧
             (q 1 1 = 1) := by
  simp

@[simp]
noncomputable
-- qq means "qubit, qubit", - 2 qubits
def qq(val1 val2: CV): StateReg2 :=
  TensorProduct.tmul ℂ (q val1) (q val2)

-- short names for 2-qubit states
@[simp]
noncomputable
def s00 := qq 0 0
@[simp]
noncomputable
def s01 := qq 0 1
@[simp]
noncomputable
def s10 := qq 1 0
@[simp]
noncomputable
def s11 := qq 1 1

-- qi means "qubit indexed". These are "classical" states of
-- indexed qubit.
--
-- qi takes 2 arguments:
-- First: qubit value
-- Second: qubit index, - qubit "address"
def qi(val: CV)(i: Fin 3): StateReg1Ind i :=
match val with
-- analog of state of classical bit with value 0
| 0 => match i with
       | 0 => fun x: X1 => match x with
                          | X1.a => 1
                          | X1.b => 0
       | 1 => fun x: X2 => match x with
                          | X2.a => 1
                          | X2.b => 0
       | 2 => fun x: X3 => match x with
                          | X3.a => 1
                          | X3.b => 0
-- analog of state of classical bit with value 1
| 1 => match i with
       | 0 => fun x: X1 => match x with
                          | X1.a => 0
                          | X1.b => 1
       | 1 => fun x: X2 => match x with
                          | X2.a => 0
                          | X2.b => 1
       | 2 => fun x: X3 => match x with
                          | X3.a => 0
                          | X3.b => 1

-- qq means 2 qubits
@[simp]
noncomputable
def qqi(val1 val2: CV)(i1 i2: Fin 3)(ord: i1 < i2):
  StateReg2Ind i1 i2 ord :=
  TensorProduct.tmul ℂ (qi val1 i1) (qi val2 i2)

-- qqq means 3 qubits
@[simp]
noncomputable
def qqq(val1 val2 val3: CV): StateReg3 :=
TensorProduct.tmul ℂ
                   (qqi val1 val2 0 1 (by aesop))
                   (qi val3 2)

-- short names for 3-qubit states
@[simp]
noncomputable
def s000 := qqq 0 0 0
@[simp]
noncomputable
def s001 := qqq 0 0 1
@[simp]
noncomputable
def s010 := qqq 0 1 0
@[simp]
noncomputable
def s011 := qqq 0 1 1
@[simp]
noncomputable
def s100 := qqq 1 0 0
@[simp]
noncomputable
def s101 := qqq 1 0 1
@[simp]
noncomputable
def s110 := qqq 1 1 0
@[simp]
noncomputable
def s111 := qqq 1 1 1
