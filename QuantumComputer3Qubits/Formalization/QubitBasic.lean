import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
-- This file formlizes single qubit state and its attributes.

@[reducible]
def QubitState:Type := Fin 2 → ℂ

-- Quantum analog of a qubit containing 0
def QZero:QubitState := fun x:Fin 2 => match x with
                                       | 0 => 1
                                       | 1 => 0

-- Quantum analog of a qubit containing 1
def QOne:QubitState := fun x:Fin 2 => match x with
                                      | 0 => 0
                                      | 1 => 1

-- Inner product explicitly defined for qubit state type.
-- Qubit state is the only type we explicitly define inner
-- product for.
-- Inner product for all other types is automatically derived
-- from this inner product through mechanisms for linearly
-- isomorphic types and for tensor products of types.
instance QubitStateInnerProduct: IP QubitState :=
{
  f(s1 s2: QubitState) := (star (s1 0)) * (s2 0) + (star (s1 1)) * (s2 1)
  comm := by
    intro v w
    generalize rv0: v 0 = v0
    generalize rv1: v 1 = v1
    generalize rw0: w 0 = w0
    generalize rw1: w 1 = w1
    clear rv0 rv1 rw0 rw1 v w
    rw [ComplexUtil.DistrSumStar]
    rw [ComplexUtil.DistrMultStar]
    rw [ComplexUtil.DistrMultStar]
    rw [ComplexUtil.DoubleStar]
    rw [ComplexUtil.DoubleStar]
    ring
  distrRight := by
    intro v w₁ w₂
    have eq:∀i: Fin 2, (w₁ + w₂) i = w₁ i + w₂ i := by
      aesop
    rw [eq]
    rw [eq]
    ring
  smulRight := by
    intro v w m
    have eq:∀i: Fin 2, (m • w) i = m * (w i) := by
      aesop
    rw [eq]
    rw [eq]
    ring
  self := by
    intro v
    generalize r0: v 0 = c0
    generalize r1: v 1 = c1
    clear v r0 r1
    simp
    ring
}

-- Orthonormal basis explicitly defined for qubit state.
-- Qubit state is the only type we explicitly define
-- orthonormal basis for.
-- Orthonormal basis for all other types is (semi-)automatically
-- derived from this orhtonormal basis through mechanisms
-- for linearly isomorphic types and for tensor products of types.
noncomputable
instance QubitStateOrthonormalBasis: OB.OrthonormalBasisImpl QubitState 2 :=
{
  basis := Pi.basisFun ℂ (Fin 2)
  prop := by
    intro i j
    fin_cases i
    all_goals fin_cases j
    all_goals simp [IP.f]
}
