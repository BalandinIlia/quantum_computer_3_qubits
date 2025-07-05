import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Control.Monad.Basic
import Mathlib.Control.Applicative
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.Nat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FiniteSpan
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import QuantumComputer3Qubits.Formalization.QubitBasic
import QuantumComputer3Qubits.Formalization.QubitIndexed
import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.LinearEquivRegistryState

/-

open scoped TensorProduct

noncomputable
def isoQubitPair(i1 i2: Fin 3)(neq: (i1 < i2)):
  (StateReg2Ind i1 i2 neq) ≃ₗ[ℂ] (TensorProduct ℂ QubitState QubitState) := by
  simp [StateReg2Ind]
  exact TensorProduct.congr (isoQubitIndQubitBase i1) (isoQubitIndQubitBase i2)

@[reducible]
def opPure1:Type := QubitState →ₗ[ℂ] QubitState
@[reducible]
def opPure2:Type := (TensorProduct ℂ QubitState QubitState) →ₗ[ℂ] (TensorProduct ℂ QubitState QubitState)
@[reducible]
def opContext2(i1 i2: Fin 3)(neq: (i1 < i2)):Type := (StateReg2Ind i1 i2 neq) →ₗ[ℂ] (StateReg2Ind i1 i2 neq)
@[reducible]
def opContext1(i1: Fin 3):Type := (StateReg1Ind i1) →ₗ[ℂ] (StateReg1Ind i1)

noncomputable
def opContext1Id(i1: Fin 3): opContext1 i1 :=
{
  toFun(q: (StateReg1Ind i1)) := q
  map_add' := by aesop
  map_smul' := by aesop
}

def opFull:Type := StateReg3 →ₗ[ℂ] StateReg3

noncomputable
def liftt(i1 i2: Fin 3)(neq: (i1 < i2))(op: opPure2): opContext2 i1 i2 neq :=
{
  toFun(st: (StateReg2Ind i1 i2 neq)) := by
    let stP:(TensorProduct ℂ QubitState QubitState) := (isoQubitPair i1 i2 neq) st
    let ftP:(TensorProduct ℂ QubitState QubitState) := op stP
    exact ((isoQubitPair i1 i2 neq).symm ftP)
  map_add' := by
    intro x y
    simp
  map_smul' := by
    simp
}

noncomputable
def TP(i1 i2: Fin 3)
      (neq: (i1 < i2))
      (i3: Fin 3)
      (neq2: ¬(i3=i1))
      (neq3: ¬(i3=i2))
      (o1: opContext1 i3)
      (o2: opContext2 i1 i2 neq): StateReg3 →ₗ[ℂ] StateReg3 :=
{
  toFun(s:StateReg3):StateReg3 := by
    let stP:(StateReg2Ind i1 i2 neq) ⊗[ℂ] (StateReg1Ind i3) := (iso2 i1 i2 neq i3 neq2 neq3).symm s
    let ftP:(StateReg2Ind i1 i2 neq) ⊗[ℂ] (StateReg1Ind i3) := (TensorProduct.map o2 o1) stP
    exact (iso2 i1 i2 neq i3 neq2 neq3) ftP
  map_add' := by
    intro x y
    simp [(iso2 i1 i2 neq i3 neq2 neq3).symm.map_add]
  map_smul' := by
    intro x y
    simp [(iso2 i1 i2 neq i3 neq2 neq3).symm.map_smul]
}

noncomputable
def mul:opPure1:=
{
  toFun(s: QubitState) := 2•s
  map_add' := by
    intro x y
    module
  map_smul' := by
    intro m x
    simp
}

def idPur1:opPure1:=
{
  toFun(s: QubitState) := s
  map_add' := by
    intro x y
    module
  map_smul' := by
    intro m x
    simp
}

noncomputable
def hmull:opPure2 := TensorProduct.map mul idPur1

noncomputable
def hmulr:opContext2 0 2 (by aesop):=liftt 0 2 (by aesop) hmull

#check TP 0 2 (by aesop) 1 (by aesop) (by aesop) (opContext1Id 1) hmulr
noncomputable
def operFin:=TP 0 2 (by aesop) 1 (by aesop) (by aesop) (opContext1Id 1) hmulr

theorem th:
  ∀q0: QubitInd 0,
  ∀q1: QubitInd 1,
  ∀q2: QubitInd 2,
  operFin (TensorProduct.tmul ℂ (TensorProduct.tmul ℂ q0 q1) q2) =
  (TensorProduct.tmul ℂ (TensorProduct.tmul ℂ (2•q0) q1) q2) := by
  intro q0 q1 q2
  simp [operFin]
  simp [TP]
  simp [hmulr]
  simp [liftt]
  simp [iso2]
  simp [opContext1Id]
  simp [isoQubitPair]
  simp [hmull]
  simp [idPur1]
  simp [mul]
  simp [isoQubitIndQubitBase]
  have eq: 2 * q0 =(fun x:X1 => match x with
            | X1.a => Mul.mul 2 (q0 X1.a)
            | X1.b => Mul.mul 2 (q0 X1.b)) := by
    aesop
  rw [eq]
  aesop
-/
