import QuantumComputer3Qubits.QubitBasic

inductive X1
| a: X1
| b: X1

inductive X2
| a: X2
| b: X2

inductive X3
| a: X3
| b: X3

@[reducible]
def QubitInd(n: Fin 3):Type := match n with
| 0 => X1 → ℂ
| 1 => X2 → ℂ
| 2 => X3 → ℂ

def isoQubitIndQubitBase(i: Fin 3): ((QubitInd i) ≃ QubitState) :=
{
  toFun := fun (q:QubitInd i) =>
    match i with
    | 0 => fun x:Fin 2 => match x with
                          | 0 => q X1.a
                          | 1 => q X1.b
    | 1 => fun x:Fin 2 => match x with
                          | 0 => q X2.a
                          | 1 => q X2.b
    | 2 => fun x:Fin 2 => match x with
                          | 0 => q X3.a
                          | 1 => q X3.b
  invFun := fun (q:QubitState) =>
    match i with
    | 0 => fun x:X1 => match x with
                       | X1.a => q 0
                       | X1.b => q 1
    | 1 => fun x:X2 => match x with
                       | X2.a => q 0
                       | X2.b => q 1
    | 2 => fun x:X3 => match x with
                       | X3.a => q 0
                       | X3.b => q 1
  left_inv := by
    fin_cases i
    all_goals simp
    all_goals simp [Function.LeftInverse]
    all_goals intro x
    all_goals ext y
    all_goals cases y
    all_goals simp
  right_inv := by
    fin_cases i
    all_goals simp
    all_goals simp [Function.RightInverse, Function.LeftInverse]
    all_goals intro x
    all_goals ext y
    all_goals fin_cases y
    all_goals simp
}

@[reducible]
instance QubitIndMonoid(i:Fin 3):AddCommMonoid (QubitInd i) := Equiv.addCommMonoid (isoQubitIndQubitBase i)
@[reducible]
instance QubitIndModule(i:Fin 3):Module ℂ (QubitInd i) := Equiv.module ℂ (isoQubitIndQubitBase i)
