import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.OuterProduct

def conj{T: Type}
        [AddCommMonoid T]
        [Module ℂ T]
        [IP T]
        (A B: T →ₗ[ℂ] T):Prop := ∀x y: T, IP.f (B x) y = IP.f x (A y)

noncomputable
def operI{T: Type}
          [AddCommMonoid T]
          [Module ℂ T]
          [IP T]
          [ob: OrthonormalBasis T]
          (A: T →ₗ[ℂ] T)
          (i: Fin ob.N):T →ₗ[ℂ] T := OP (A (ob.basis i)) (ob.basis i)

noncomputable
def operIC{T: Type}
          [AddCommMonoid T]
          [Module ℂ T]
          [IP T]
          [ob: OrthonormalBasis T]
          (A: T →ₗ[ℂ] T)
          (i: Fin ob.N):T →ₗ[ℂ] T := OP (ob.basis i) (A (ob.basis i))

theorem th1{T: Type}
          [AddCommMonoid T]
          [Module ℂ T]
          [IP T]
          [ob: OrthonormalBasis T]
          (A: T →ₗ[ℂ] T)
          (i: Fin ob.N): conj (operI A i) (operIC A i) := by
  simp [conj]
  intro x y
  simp [operI, operIC]
  simp [OP]
  simp [IP.smulLeft]
  simp [IP.smulRight]
  rw [IP.comm x]
  generalize r1: (IP.f (A (OrthonormalBasis.basis i)) x) = c1
  generalize r2: IP.f (OrthonormalBasis.basis i) y = c2
  rw [ComplexUtil.Aux]
  ring

noncomputable
def her{T: Type}
       [AddCommMonoid T]
       [Module ℂ T]
       [IP T]
       [ob: OrthonormalBasis T]
       (A: T →ₗ[ℂ] T):T →ₗ[ℂ] T :=
finsum (fun i: Fin ob.N => operIC A i)

theorem the1(T: Type)
       [AddCommMonoid T]
       [Module ℂ T]
       [IP T]
       [ob: OrthonormalBasis T]
       (A B: T →ₗ[ℂ] T): her (A+B) = (her A) + (her B) := by
  simp [her]
  have eq: ∀i: Fin ob.N, operIC (A + B) i = (operIC A i) + (operIC B i) := by
    intro i
    simp [operIC]
    ext x
    simp [OP]
    simp [IP.distrLeft]
    generalize r1: IP.f (A (OrthonormalBasis.basis i)) x = c1
    generalize r2: IP.f (B (OrthonormalBasis.basis i)) x = c2
    module
  simp [eq]
  generalize rA: operIC A = AA
  generalize rB: operIC B = BB

  apply @finsum_add_distrib (Fin ob.N) (T →ₗ[ℂ] T) _ AA BB

  apply Set.toFinite (Function.support AA)
  apply Set.toFinite (Function.support BB)
