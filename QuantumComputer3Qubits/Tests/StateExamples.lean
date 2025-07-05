import QuantumComputer3Qubits.Formalization.RegistryState

-- SE means "State Examples"
namespace SE

@[simp]
def s0: StateReg1 :=
fun x:Fin 2 => match x with
| 0 => 1
| 1 => 0
@[simp]
def s1: StateReg1 :=
fun x:Fin 2 => match x with
| 0 => 0
| 1 => 1

@[simp]
noncomputable
def s00: StateReg2 := TensorProduct.tmul ℂ QZero QZero
@[simp]
noncomputable
def s01: StateReg2 := TensorProduct.tmul ℂ QZero QOne
@[simp]
noncomputable
def s10: StateReg2 := TensorProduct.tmul ℂ QOne QZero
@[simp]
noncomputable
def s11: StateReg2 := TensorProduct.tmul ℂ QOne QOne

@[simp]
def QZeroInd(i: Fin 3): StateReg1Ind i :=
match i with
| 0 => fun x: X1 => match x with
                    | X1.a => 1
                    | X1.b => 0
| 1 => fun x: X2 => match x with
                    | X2.a => 1
                    | X2.b => 0
| 2 => fun x: X3 => match x with
                    | X3.a => 1
                    | X3.b => 0

@[simp]
def QOneInd(i: Fin 3): StateReg1Ind i :=
match i with
| 0 => fun x: X1 => match x with
                    | X1.a => 0
                    | X1.b => 1
| 1 => fun x: X2 => match x with
                    | X2.a => 0
                    | X2.b => 1
| 2 => fun x: X3 => match x with
                    | X3.a => 0
                    | X3.b => 1
