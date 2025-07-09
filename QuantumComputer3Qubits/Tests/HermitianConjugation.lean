import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.HermitianConjugation

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
∀i: Fin ob.N, isAdj (operCompConj A i) (operComp A i) := by
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

-- Check that adj is distributive
theorem test2(T: Type)
             [AddCommMonoid T]
             [Module ℂ T]
             [IP T]
             [ob: OrthonormalBasis T]
             (A B: T →ₗ[ℂ] T):
adj (A+B) = (adj A) + (adj B) := by
  simp [adj]
  have eq: ∀i: Fin ob.N, operCompAdj (A + B) i = (operCompAdj A i) + (operCompAdj B i) := by
    intro i
    simp [operCompAdj]
    ext x
    simp [OP]
    simp [IP.distrLeft]
    generalize r1: IP.f (A (OrthonormalBasis.basis i)) x = c1
    generalize r2: IP.f (B (OrthonormalBasis.basis i)) x = c2
    module
  simp [eq]
  generalize rA: operCompAdj A = AA
  generalize rB: operCompAdj B = BB
  apply @finsum_add_distrib (Fin ob.N) (T →ₗ[ℂ] T) _ AA BB
  apply Set.toFinite (Function.support AA)
  apply Set.toFinite (Function.support BB)

private axiom ax1{T: Type}
                 [AddCommMonoid T]
                 [Module ℂ T]
                 (N: ℕ)
                 (A: Fin N → (T →ₗ[ℂ] T))
                 (x: T):
(finsum A) x = finsum (fun i: Fin N => A i x)

private axiom ax2(T: Type)
                 [AddCommMonoid T]
                 (N: ℕ)
                 (op: T → T → ℂ)
                 (opPR1: ∀x1 x2 y: T, op (x1+x2) y = op x1 y + op x2 y)
                 (opPR2: ∀x y1 y2: T, op x (y1+y2) = op x y1 + op x y2)
                 (S: Fin N → T)
                 (x: T):
op (finsum S) x = finsum (fun i: Fin N => op (S i) x)

private axiom ax3(T: Type)
                 [AddCommMonoid T]
                 (N: ℕ)
                 (op: T → T → ℂ)
                 (opPR1: ∀x1 x2 y: T, op (x1+x2) y = op x1 y + op x2 y)
                 (opPR2: ∀x y1 y2: T, op x (y1+y2) = op x y1 + op x y2)
                 (S: Fin N → T)
                 (x: T):
op x (finsum S) = finsum (fun i: Fin N => op x (S i))

private axiom ax4{T: Type}
                 [AddCommMonoid T]
                 [Module ℂ T]
                 (N: ℕ)
                 (A: (T →ₗ[ℂ] T))
                 (x: Fin N → T):
A (finsum x) = finsum (fun i: Fin N => A (x i))

private axiom ax5(T: Type)
                 [AddCommMonoid T]
                 (N: ℕ)
                 (S: Fin N → Fin N → T):
finsum (fun i: Fin N => finsum (fun j: Fin N => if(i=j) then S j i else 0)) =
finsum (fun i: Fin N => S i i)

private axiom ax6(T: Type)
                 [AddCommMonoid T]
                 [Module ℂ T]
                 (N: ℕ)
                 (bas: Basis (Fin N) ℂ T):
∀x: T, x = finsum (fun i: Fin N => (Basis.repr bas x i) • (bas i))

-- check that conjugate is really conjugate
private theorem test3{T: Type}
             [AddCommMonoid T]
             [Module ℂ T]
             [IP T]
             [ob: OrthonormalBasis T]
             (A: T →ₗ[ℂ] T): isAdj A (adj A) := by
  simp [isAdj, adj, operCompAdj, OP]
  intro x y
  simp [ax1]
  rw [ax2 T ob.N (IP.f) IP.distrLeft IP.distrRight (fun i:Fin ob.N => IP.f (A (OrthonormalBasis.basis i)) x • OrthonormalBasis.basis i) y]
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
  let pr1 := ax3 T ob.N (IP.f) IP.distrLeft IP.distrRight (fun i:Fin ob.N => ((OP (A (OrthonormalBasis.basis i)) (OrthonormalBasis.basis i)) y)) x
  simp [Eq.symm pr1]
  clear pr1 eq
  have eq: finsum (fun i : Fin ob.N => (OP (A (OrthonormalBasis.basis i)) (OrthonormalBasis.basis i)) y) = A y := by
    rw [ax6 T ob.N ob.basis y]
    simp [ax4]
    simp [OP]
    simp [ob.prop]
    simp [ax5]
  simp [eq]
