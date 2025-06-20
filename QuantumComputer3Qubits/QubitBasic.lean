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
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FiniteSpan

@[reducible]
def QubitState:Type := Fin 2 → ℂ
#synth Module ℂ QubitState

noncomputable
def QubitBasis:Basis (Fin 2) ℂ QubitState := Pi.basisFun ℂ (Fin 2)

def QZero:QubitState := fun x:Fin 2 => match x with
                                       | 0 => 1
                                       | 1 => 0

def QOne:QubitState := fun x:Fin 2 => match x with
                                      | 0 => 0
                                      | 1 => 1

instance QubitStateInhab: Inhabited QubitState :=
{
  default := QZero
}

--#check trace_eq_sum_inner

open scoped WithLp
open scoped InnerProductSpace

#check InnerProductSpace
#synth InnerProductSpace ℂ (WithLp 2 (ℂ × ℂ))
