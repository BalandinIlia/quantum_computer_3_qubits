import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.FiniteSum

namespace Test_HermitianConjugation
open HC

-- proposition that B is adjoint of A
def isAdj{T: Type}
         [AddCommMonoid T]
         [Module ℂ T]
         [IP T]
         (A B: T →ₗ[ℂ] T): Prop :=
         ∀x y: T, IP.f (B x) y = IP.f x (A y)

-- check that adjoint operator component is really adjoint
theorem test1{T: Type}
             [AddCommMonoid T]
             [Module ℂ T]
             [IP T]
             [ob: OrthonormalBasis T]
             (A: T →ₗ[ℂ] T):
∀i: Fin ob.N, isAdj (operCompAdj A i) (operComp A i) := by
  intro i
  simp [isAdj, operComp, operCompAdj, OP]
  intro x y
  simp [IP.smulLeft, IP.smulRight]
  simp [IP.comm x]
  generalize r₁: (IP.f (OrthonormalBasis.basis i) x) = c₁
  generalize r₂: IP.f (A (OrthonormalBasis.basis i)) y = c₂
  clear r₁ r₂
  clear A i x y
  ring

-- check that conjugate is really conjugate
private theorem test2{T: Type}
             [AddCommMonoid T]
             [Module ℂ T]
             [IP T]
             [ob: OrthonormalBasis T]
             (pos: ob.N > 0)
             (A: T →ₗ[ℂ] T): isAdj A (adj A) := by
  simp [isAdj, adj, operCompAdj, OP]
  intro x y
  simp [FS.applyMap]
  rw [FS.distrLeft T ob.N (IP.f) IP.distrLeft (by sorry) (fun i:Fin ob.N => IP.f (A (OrthonormalBasis.basis i)) x • OrthonormalBasis.basis i) y]
  simp [IP.smulLeft, IP.smulRight]
  simp [IP.comm _ x]
  have eq: ∀i: Fin ob.N,
           IP.f x (A (OrthonormalBasis.basis i)) *
           IP.f (OrthonormalBasis.basis i) y =
           IP.f x (OP (A (ob.basis i)) (ob.basis i) y) := by
    simp [OP]
    simp [IP.smulLeft, IP.smulRight]
    ring_nf
    aesop
  simp [eq]
  let pr1 := FS.distrRight T ob.N (IP.f) IP.distrRight (by sorry) (fun i:Fin ob.N => ((OP (A (OrthonormalBasis.basis i)) (OrthonormalBasis.basis i)) y)) x
  simp [Eq.symm pr1]
  clear pr1 eq
  have eq: FS.fs (fun i : Fin ob.N => (OP (A (OrthonormalBasis.basis i)) (OrthonormalBasis.basis i)) y) = A y := by
    rw [FS.basis T ob.N pos ob.basis y]
    simp [FS.applyDistr]
    simp [OP]
    simp [ob.prop]
    simp [FS.doubleFS T ob.N pos]
  simp [eq]
