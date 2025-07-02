import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import QuantumComputer3Qubits.Formalization.InnerProduct

@[reducible]
def QubitState:Type := Fin 2 → ℂ

noncomputable
def QubitBasis:Basis (Fin 2) ℂ QubitState := Pi.basisFun ℂ (Fin 2)

def QZero:QubitState := fun x:Fin 2 => match x with
                                       | 0 => 1
                                       | 1 => 0

def QOne:QubitState := fun x:Fin 2 => match x with
                                      | 0 => 0
                                      | 1 => 1

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
}
