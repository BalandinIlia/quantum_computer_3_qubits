import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import QuantumComputer3Qubits.Complex

class IP(M: Type)[AddCommMonoid M][mod: Module ℂ M] where
  f: M → M → ℂ
  comm: ∀v w: M, (f v w) = star (f w v)
  distrRight: ∀v w₁ w₂: M, (f v (w₁ + w₂)) = (f v w₁) + (f v w₂)
  smulRight: ∀v w: M, ∀m: ℂ, (f v (m • w)) = m * (f v w)

namespace IP

lemma distrLeft {M: Type}[AddCommMonoid M][Module ℂ M][IP M]
                (v₁ v₂ w: M):
  (IP.f (v₁ + v₂) w) = (IP.f v₁ w) + (IP.f v₂ w) := by
  rw [IP.comm]
  rw [IP.distrRight]
  rw [ComplexUtil.DistrSumStar]
  rw [IP.comm w v₁]
  rw [IP.comm w v₂]
  simp

lemma smulLeft{M: Type}[AddCommMonoid M][Module ℂ M][IP M]
              (m: ℂ)(v w: M):
  (IP.f (m • v) w) = (star m) * (IP.f v w) := by
  rw [IP.comm]
  rw [IP.smulRight]
  rw [IP.comm]
  simp

open scoped TensorProduct

def mult1(M N: Type)
  [AddCommMonoid M][modM: Module ℂ M][ipM: IP M]
  [AddCommMonoid N][modN: Module ℂ N][ipN: IP N]
  (m: M)(n: N): M →ₗ[ℂ] (N →ₗ[ℂ] ℂ) :=
{
  toFun := by
    intro m₂
    exact
    {
      toFun := by
        intro n₂
        exact (ipM.f m m₂)*(ipN.f n n₂)
      map_add' := by
        intro x y
        rw [IP.distrRight]
        ring
      map_smul' := by
        intro m₁ x
        rw [IP.smulRight]
        simp
        ring
    }
  map_add' := by
    intro x y
    ext g
    simp
    rw [IP.distrRight]
    ring
  map_smul' := by
    intro m₁ x
    ext g
    simp
    rw [IP.smulRight]
    ring
}

noncomputable
def mult2(M N: Type)
  [AddCommMonoid M][modM: Module ℂ M][ipM: IP M]
  [AddCommMonoid N][modN: Module ℂ N][ipN: IP N]
  (mn: M ⊗[ℂ] N): M →ₗ[ℂ] (N →ₗ[ℂ] ℂ) :=
{
  toFun := by
    intro m
    exact
    {
      toFun := by
        intro n
        exact  star (TensorProduct.lift (mult1 M N m n) mn)
      map_add' := by
        intro x y
        rw [ComplexUtil.DistrInvSumStar]
        apply ComplexUtil.EqStar
        apply TensorProduct.induction_on
            (motive := fun z: M ⊗[ℂ] N => (TensorProduct.lift (mult1 M N m (x + y))) z =
            (TensorProduct.lift (mult1 M N m x)) z + (TensorProduct.lift (mult1 M N m y)) z)
        aesop
        {
          simp [mult1, distrLeft]
          ring_nf
          aesop
        }
        {
          intro x₁ y₁
          intro h₁ h₂
          simp [LinearMap.map_add]
          simp [h₁, h₂]
          ring
        }
      map_smul' := by
        intro x n
        apply TensorProduct.induction_on
            (motive := fun z: M ⊗[ℂ] N =>
            star ((TensorProduct.lift (mult1 M N m (x • n))) z) =
            (RingHom.id ℂ) x • star ((TensorProduct.lift (mult1 M N m n)) z))
        aesop
        {
          simp [mult1, smulLeft]
          ring_nf
          aesop
        }
        {
          intro x₁ y
          intro h₁ h₂
          rw [LinearMap.map_add]
          rw [LinearMap.map_add]
          simp [h₁, h₂]
          rw [ComplexUtil.Aux]
          rw [ComplexUtil.Aux]
          ring
        }
    }
  map_add' := by
    intro x y
    ext g
    simp
    rw [ComplexUtil.Aux]
    rw [ComplexUtil.Aux]
    rw [ComplexUtil.Aux]
    rw [ComplexUtil.DistrInvSumStar]
    apply ComplexUtil.EqStar
    apply TensorProduct.induction_on
        (motive := fun z: M ⊗[ℂ] N =>
        (TensorProduct.lift (mult1 M N (x + y) g)) z =
        (TensorProduct.lift (mult1 M N x g)) z + (TensorProduct.lift (mult1 M N y g)) z)
    aesop
    {
      simp [mult1, distrLeft]
      ring_nf
      aesop
    }
    {
      intro x₁ y₁
      intro h₁ h₂
      simp [LinearMap.map_add]
      simp [h₁, h₂]
      ring
    }
  map_smul' := by
    intro m x
    ext g
    simp
    rw [ComplexUtil.Aux]
    rw [ComplexUtil.Aux]
    apply TensorProduct.induction_on
        (motive := fun z: M ⊗[ℂ] N =>
        star ((TensorProduct.lift (mult1 M N (m • x) g)) z) =
        m * star ((TensorProduct.lift (mult1 M N x g)) z))
    aesop
    {
      simp [mult1]
      intro x₁ y
      rw [smulLeft]
      rw [ComplexUtil.Aux]
      rw [ComplexUtil.Aux]
      rw [ComplexUtil.Aux]
      rw [ComplexUtil.DistrMultStar]
      simp
      ring
    }
    {
      intro x₁ y
      intro h₁ h₂
      rw [LinearMap.map_add]
      rw [LinearMap.map_add]
      simp [h₁, h₂]
      rw [ComplexUtil.Aux]
      rw [ComplexUtil.Aux]
      ring
    }
}

lemma mult2Lin(M N: Type)
  [AddCommMonoid M][modM: Module ℂ M][ipM: IP M]
  [AddCommMonoid N][modN: Module ℂ N][ipN: IP N]
  (x y: M ⊗[ℂ] N): mult2 M N (x+y) = mult2 M N x + mult2 M N y := by
  simp [mult2]
  ext a b
  simp

lemma fgh{M : Type}
         {N : Type}
         {P : Type}
         [inst_1 : AddCommMonoid M]
         [inst_2 : AddCommMonoid N]
         [inst_3 : AddCommMonoid P]
         [inst_4 : Module ℂ M]
         [inst_5 : Module ℂ N]
         [inst_6 : Module ℂ P]
         (m1: M →ₗ[ℂ] N →ₗ[ℂ] P)
         (m2: M →ₗ[ℂ] N →ₗ[ℂ] P):
  TensorProduct.lift (m1+m2) =
  TensorProduct.lift m1 + TensorProduct.lift m2 := by
  aesop

noncomputable
instance tensorProductIP(T₁ T₂: Type)
  [AddCommMonoid T₁][modM: Module ℂ T₁][ipM: IP T₁]
  [AddCommMonoid T₂][modN: Module ℂ T₂][ipN: IP T₂]:
  IP (T₁ ⊗[ℂ] T₂) :=
{
  f := by
    intro inp1
    intro inp2
    exact (TensorProduct.lift (mult2 T₁ T₂ inp1) inp2)
  comm := by
    intro v w
    --rw [ComplexUtil.DoubleStar]
    --apply Eq.symm
    let pr(x y: T₁ ⊗[ℂ] T₂):Prop:=
        (TensorProduct.lift (mult2 T₁ T₂ x)) y = star ((TensorProduct.lift (mult2 T₁ T₂ y)) x)
    have lem(x y: T₁ ⊗[ℂ] T₂): pr x y ↔ pr y x := by
      aesop
    have lem2(x y z: T₁ ⊗[ℂ] T₂): (pr x y ∧ pr x z) → pr x (y+z)  := by
      simp [pr, mult2Lin]
      rw [fgh]
      aesop
    have fol: pr v w → (TensorProduct.lift (mult2 T₁ T₂ v)) w = star ((TensorProduct.lift (mult2 T₁ T₂ w)) v) := by
      aesop
    apply fol
    clear fol
    apply TensorProduct.induction_on
        (motive := fun x:T₁ ⊗[ℂ] T₂ => pr x w)
    apply TensorProduct.induction_on
        (motive := fun y:T₁ ⊗[ℂ] T₂ => pr 0 y)
    aesop
    simp [pr, mult2]
    aesop
    apply TensorProduct.induction_on
        (motive := fun z:T₁ ⊗[ℂ] T₂ => ∀ (x : T₁) (y : T₂), pr (x ⊗ₜ[ℂ] y) z)
    simp [pr, mult2]
    {
      simp [pr, mult2, mult1]
      intro x y x₁ y₁
      rw [IP.comm]
      rw [IP.comm y y₁]
      simp
    }
    {
      simp [pr]
      simp [mult2Lin]
      aesop
    }


    intro x y
    intro h1 h2
    rw [lem (x+y) w]
    rw [lem] at h1
    rw [lem] at h2
    revert h1 h2
    revert x y


    apply TensorProduct.induction_on
        (motive := fun z:T₁ ⊗[ℂ] T₂ => ∀ (x y : T₁ ⊗[ℂ] T₂), pr z x → pr z y → pr z (x + y))
    aesop
    {
      simp [pr, mult2Lin]
      aesop
    }
    {
      intro x y
      --simp [pr]
      intro h₁ h₂
      intro x₁ y₁
      intro h₃ h₄
      apply lem2
      aesop
    }
  distrRight := by
    intro v w₁ w₂
    --rw [ComplexUtil.StarDistr2 ((TensorProduct.lift (mult2 T₁ T₂ v)) w₁) ((TensorProduct.lift (mult2 T₁ T₂ v)) w₂)]
    --apply ComplexUtil.RemStar
    simp [LinearMap.map_add]
  smulRight := by
    intro v w m
    apply TensorProduct.induction_on (motive :=
        fun x:T₁ ⊗[ℂ] T₂ =>
        ((TensorProduct.lift (mult2 T₁ T₂ v)) (m • x)) =
        m * ((TensorProduct.lift (mult2 T₁ T₂ v)) x)
    )
    aesop
    simp
    simp [LinearMap.map_add]
    ring_nf
    aesop
  /-self2 := by
    intro v
    apply Iff.intro
    apply TensorProduct.induction_on (motive :=
        fun x: T₁ ⊗[ℂ] T₂ =>
        (TensorProduct.lift (mult2 T₁ T₂ x)) x = 0 → x = 0
    )
    aesop
    {
      simp [mult2, mult1]
      intro x y h
      have folX: IP.f x x = 0 → x=0 := by
        rw [IP.self2]
        aesop
      have folY: IP.f y y = 0 → y=0 := by
        rw [IP.self2]
        aesop
      have eq: x = 0 ∨ y = 0 := by
        aesop
      aesop
    }
    {
      simp [LinearMap.map_add]
      simp [mult2Lin]
      simp [fgh]
    }-/
}
