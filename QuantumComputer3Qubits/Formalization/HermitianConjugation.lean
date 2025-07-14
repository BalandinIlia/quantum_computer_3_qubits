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
         [OrthonormalBasis T]
         (A B: T →ₗ[ℂ] T): Prop :=
         ∀x y: T, IP.f (B x) y = IP.f x (A y)

lemma commAdj{T: Type}
         [AddCommMonoid T]
         [Module ℂ T]
         [IP T]
         [OrthonormalBasis T]
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
  let st := @FS.Kronecker2 T _ ob.N pos (fun i: Fin ob.N => fun i_1: Fin ob.N => (OrthonormalBasis.basis.repr s) i • A (OrthonormalBasis.basis i_1))
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

-- check that adjoint is really adjoint
theorem reallyAdj{T: Type}
                 [AddCommMonoid T]
                 [Module ℂ T]
                 [IP T]
                 [ob: OrthonormalBasis T]
                 (A: T →ₗ[ℂ] T): isAdj A (adj A) := by
  simp [isAdj, adj, operCompAdj, OP]
  intro x y
  simp [FS.applyMap]
  rw [FS.distrLeft (IP.f) IP.distrLeft IP.smulLeft (fun i:Fin ob.N => IP.f (A (OrthonormalBasis.basis i)) x • OrthonormalBasis.basis i) y]
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
  let pr1 := FS.distrRight (IP.f) IP.distrRight (by intro m x y; apply IP.smulRight) (fun i:Fin ob.N => ((OP (A (OrthonormalBasis.basis i)) (OrthonormalBasis.basis i)) y)) x
  simp [Eq.symm pr1]
  clear pr1 eq
  have eq: FS.fs (fun i : Fin ob.N => (OP (A (OrthonormalBasis.basis i)) (OrthonormalBasis.basis i)) y) = A y := by
    rw [FS.basisReprAx ob.N pos ob.basis y]
    simp [FS.applyDistr]
    simp [OP]
    simp [ob.prop]
    rw [FS.Kronecker2 ob.N pos]
  simp [eq]

lemma adjEx!{T: Type}
            [AddCommMonoid T]
            [Module ℂ T]
            [IP T]
            [ob: OrthonormalBasis T]
            (A: T →ₗ[ℂ] T):
            ∃! B: T →ₗ[ℂ] T, isAdj A B := by
  use adj A
  apply And.intro
  {
    simp
    apply reallyAdj
    apply pos
  }
  {
    intro C
    simp
    intro h
    simp [isAdj] at h
    have h2: ∀ (x y : T), IP.f x (A y) = IP.f ((adj A) x) y := by
      intro x y
      have st := reallyAdj pos A
      simp [isAdj] at st
      aesop
    have h3: ∀ (x y : T), IP.f (C x) y = IP.f ((adj A) x) y := by
      aesop
    clear h h2
    generalize repl: adj A = B
    simp [repl] at h3
    clear repl A
    ext a
    let h := h3 a
    generalize rB: B a = b
    generalize rC: C a = c
    rw [rB, rC] at h
    clear h3 rB rC a C B
    let reprC := FS.basisReprAx ob.N pos ob.basis c
    let reprB := FS.basisReprAx ob.N pos ob.basis b
    simp [FS.basisRepr] at reprB reprC
    have repl: (∀i: Fin ob.N, Basis.repr ob.basis b i = Basis.repr ob.basis c i) → c = b := by
      intro h
      rw [reprB, reprC]
      simp [h]
    apply repl
    clear repl
    rw [reprB, reprC] at h
    clear reprB reprC
    intro i
    let hh := h (ob.basis i)
    let stC := @FS.distrLeft T _ _ ob.N IP.f IP.distrLeft IP.smulLeft (fun i => (ob.basis.repr c) i • ob.basis i) (ob.basis i)
    let stB := @FS.distrLeft T _ _ ob.N IP.f IP.distrLeft IP.smulLeft (fun i => (ob.basis.repr b) i • ob.basis i) (ob.basis i)
    rw [stC, stB] at hh
    clear stB stC
    simp [IP.smulLeft] at hh
    simp [ob.prop] at hh
    have Kron: ∀ (F : Fin ob.N → ℂ), (FS.fs fun i_1 => if i_1 = i then F i_1 else 0) = F i := by
      intro F
      have st := @FS.Kronecker ℂ _ ob.N pos i F
      rw [Eq.symm st]
      have repl: ∀i j: Fin ob.N, (i=j) ↔ (j=i) := by aesop
      aesop
    simp [Kron] at hh
    clear h Kron
    generalize replBB: (OrthonormalBasis.basis.repr b) i = bb
    generalize replCC: (OrthonormalBasis.basis.repr c) i = cc
    simp [replBB, replCC] at hh
    clear replBB replCC b c i pos ob
    rw [ComplexUtil.Aux] at hh
    rw [ComplexUtil.Aux] at hh
    let h := ComplexUtil.EqStar (star cc) (star bb) hh
    simp [ComplexUtil.DoubleStar] at h
    apply (Eq.symm h)
}

-- helper lemma to construct adjoint operator in certain cases
-- avoiding orthonormal basis
lemma adjOP{T: Type}
         [AddCommMonoid T]
         [Module ℂ T]
         [IP T]
         [OrthonormalBasis T]
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
         [OrthonormalBasis T]
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
