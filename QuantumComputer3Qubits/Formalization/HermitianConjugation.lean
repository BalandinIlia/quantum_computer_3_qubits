import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.FiniteSum

-- HC means "Hermitian Conjugation"
namespace HC

-- definition that B is adjoint of A
def isAdj{T: Type}
         [AddCommMonoid T]
         [Module ℂ T]
         [IP T]
         (A B: T →ₗ[ℂ] T): Prop :=
         ∀x y: T, IP.f (B x) y = IP.f x (A y)

lemma commAdj{T: Type}
         [AddCommMonoid T]
         [Module ℂ T]
         [IP T]
         (A B: T →ₗ[ℂ] T):
         isAdj A B → isAdj B A := by
       simp [isAdj]
       intro h
       intro x y
       let pr := h y x
       rw [IP.comm (B y) x] at pr
       rw [IP.comm y (A x)] at pr
       let pr2 := ComplexUtil.EqStar (star (IP.f x (B y))) (star (IP.f (A x) y))
       let pr3 := pr2 pr
       simp [ComplexUtil.DoubleStar] at pr3
       simp [pr3]

-- This is kind of operator component associated with the i-th
-- vector of orthonormal basis.
-- Sum of all components is equal to the operator.
noncomputable
def operComp{T: Type}
            [AddCommMonoid T]
            [Module ℂ T]
            [IP T]
            [ob: OrthonormalBasis T]
            (A: T →ₗ[ℂ] T)
            (i: Fin ob.N): T →ₗ[ℂ] T :=
            OP (A (ob.basis i)) (ob.basis i)

lemma reprOp{T: Type}
            [AddCommMonoid T]
            [Module ℂ T]
            [IP T]
            [ob: OrthonormalBasis T]
            (pos: ob.N > 0)
            (A: T →ₗ[ℂ] T):
A = FS.fs (fun i: Fin ob.N => operComp A i) := by
       ext s
       have rt := FS.basisReprAx ob.N (by aesop) ob.basis s
       simp [FS.basisRepr] at rt
       rw [FS.applyMap]
       rw [rt]
       rw [FS.applyDistr]
       simp [FS.applyDistr]
       simp [operComp, OP]
       simp [ob.prop]
       let st := @FS.doubleFS T _ ob.N pos (fun i: Fin ob.N => fun i_1: Fin ob.N => (OrthonormalBasis.basis.repr s) i • A (OrthonormalBasis.basis i_1))
       simp [st]

-- This is an adjoint component.
noncomputable
def operCompAdj{T: Type}
               [AddCommMonoid T]
               [Module ℂ T]
               [IP T]
               [ob: OrthonormalBasis T]
               (A: T →ₗ[ℂ] T)
               (i: Fin ob.N): T →ₗ[ℂ] T :=
               OP (ob.basis i) (A (ob.basis i))

-- This is an adjoint operator formulated as a sum of adjoint components.
noncomputable
def adj{T: Type}
       [AddCommMonoid T]
       [Module ℂ T]
       [IP T]
       [ob: OrthonormalBasis T]
       (A: T →ₗ[ℂ] T): T →ₗ[ℂ] T :=
       FS.fs (fun i: Fin ob.N => operCompAdj A i)

-- helper lemma to construct adjoint operator in certain cases
-- avoiding orthonormal basis
lemma adjOP{T: Type}
         [AddCommMonoid T]
         [Module ℂ T]
         [IP T]
         (s1 s2: T):
         isAdj (OP s2 s1) (OP s1 s2) := by
       simp [isAdj, OP]
       intro x y
       simp [IP.smulLeft, IP.smulRight]
       rw [IP.comm s2 x]
       simp
       ring

-- helper lemma to construct adjoint operator in certain cases
-- avoiding orthonormal basis
lemma adjSum{T: Type}
         [AddCommMonoid T]
         [Module ℂ T]
         [IP T]
         (A Aa B Ba: T →ₗ[ℂ] T)
         (pA: isAdj Aa A)
         (pB: isAdj Ba B):
         isAdj (Aa+Ba) (A+B) := by
       simp [isAdj, OP]
       intro x y
       simp [IP.distrLeft, IP.distrRight]
       simp [isAdj] at pA pB
       let prA := pA x y
       let prB := pB x y
       simp [prA, prB]
