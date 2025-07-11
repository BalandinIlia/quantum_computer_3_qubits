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
def s00: StateReg2 := TensorProduct.tmul ℂ s0 s0
@[simp]
noncomputable
def s01: StateReg2 := TensorProduct.tmul ℂ s0 s1
@[simp]
noncomputable
def s10: StateReg2 := TensorProduct.tmul ℂ s1 s0
@[simp]
noncomputable
def s11: StateReg2 := TensorProduct.tmul ℂ s1 s1

def si0(i: Fin 3): StateReg1Ind i :=
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

def si1(i: Fin 3): StateReg1Ind i :=
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

@[simp]
noncomputable
def si00(i₁ i₂: Fin 3)(ord: i₁ < i₂):
  StateReg2Ind i₁ i₂ ord :=
  TensorProduct.tmul ℂ (si0 i₁) (si0 i₂)
@[simp]
noncomputable
def si01(i₁ i₂: Fin 3)(ord: i₁ < i₂):
  StateReg2Ind i₁ i₂ ord :=
  TensorProduct.tmul ℂ (si0 i₁) (si1 i₂)
@[simp]
noncomputable
def si10(i₁ i₂: Fin 3)(ord: i₁ < i₂):
  StateReg2Ind i₁ i₂ ord :=
  TensorProduct.tmul ℂ (si1 i₁) (si0 i₂)
@[simp]
noncomputable
def si11(i₁ i₂: Fin 3)(ord: i₁ < i₂):
  StateReg2Ind i₁ i₂ ord :=
  TensorProduct.tmul ℂ (si1 i₁) (si1 i₂)

@[simp]
noncomputable
def s000: StateReg3 := TensorProduct.tmul ℂ (si00 0 1 (by aesop)) (si0 2)
@[simp]
noncomputable
def s001: StateReg3 := TensorProduct.tmul ℂ (si00 0 1 (by aesop)) (si1 2)
@[simp]
noncomputable
def s010: StateReg3 := TensorProduct.tmul ℂ (si01 0 1 (by aesop)) (si0 2)
@[simp]
noncomputable
def s011: StateReg3 := TensorProduct.tmul ℂ (si01 0 1 (by aesop)) (si1 2)
@[simp]
noncomputable
def s100: StateReg3 := TensorProduct.tmul ℂ (si10 0 1 (by aesop)) (si0 2)
@[simp]
noncomputable
def s101: StateReg3 := TensorProduct.tmul ℂ (si10 0 1 (by aesop)) (si1 2)
@[simp]
noncomputable
def s110: StateReg3 := TensorProduct.tmul ℂ (si11 0 1 (by aesop)) (si0 2)
@[simp]
noncomputable
def s111: StateReg3 := TensorProduct.tmul ℂ (si11 0 1 (by aesop)) (si1 2)
