import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import QuantumComputer3Qubits.Formalization.ComplexUtil
-- This file formalizes inner product for arbitrary
-- vector space over the field of complex numbers.

-- IP is an abbreviation of "Inner Product"
class IP(M: Type)[AddCommMonoid M][mod: Module ℂ M] where
  f: M → M → ℂ
  comm: ∀v w: M, (f v w) = star (f w v)
  distrRight: ∀v w₁ w₂: M, (f v (w₁ + w₂)) = (f v w₁) + (f v w₂)
  smulRight: ∀v w: M, ∀m: ℂ, (f v (m • w)) = m * (f v w)
  self: ∀v: M, (f v v).im = 0

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

-- This function formalizes a double linear map.
-- The map takes two arguments: x and y and produces
-- (⟨m|⊗⟨n|)•(|x⟩⊗|y⟩) value where • stays for inner product.
-- (Here ⟨...| and |...⟩ mean Dirac notation)
def IPRight{M N: Type}
  [AddCommMonoid M][modM: Module ℂ M][ipM: IP M]
  [AddCommMonoid N][modN: Module ℂ N][ipN: IP N]
  (m: M)(n: N): M →ₗ[ℂ] (N →ₗ[ℂ] ℂ) :=
{
  toFun := by
    intro x
    exact
    {
      toFun := by
        intro y
        exact (ipM.f m x)*(ipN.f n y)
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

-- This function formalizes double linear map.
-- The map takes x and y as arguments and produces
-- star (⟨x|⊗⟨y|)•(|mn⟩) where • stays for inner product
-- We produce star (⟨x|⊗⟨y|)•(|mn⟩) and not just
-- (⟨x|⊗⟨y|)•(|mn⟩) to keep the map linear by x and y.
noncomputable
def IPLeft{M N: Type}
  [AddCommMonoid M][modM: Module ℂ M][ipM: IP M]
  [AddCommMonoid N][modN: Module ℂ N][ipN: IP N]
  (mn: M ⊗[ℂ] N): M →ₗ[ℂ] (N →ₗ[ℂ] ℂ) :=
{
  toFun := by
    intro x
    exact
    {
      toFun := by
        intro y
        exact  star (TensorProduct.lift (IPRight x y) mn)
      map_add' := by
        intro a b
        rw [ComplexUtil.DistrInvSumStar]
        apply ComplexUtil.EqStar
        apply TensorProduct.induction_on
            (motive := fun z: M ⊗[ℂ] N => (TensorProduct.lift (IPRight x (a + b))) z =
            (TensorProduct.lift (IPRight x a)) z + (TensorProduct.lift (IPRight x b)) z)
        aesop
        {
          simp [IPRight, distrLeft]
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
        intro m a
        apply TensorProduct.induction_on
            (motive := fun z: M ⊗[ℂ] N =>
            star ((TensorProduct.lift (IPRight x (m • a))) z) =
            (RingHom.id ℂ) m • star ((TensorProduct.lift (IPRight x a)) z))
        aesop
        {
          simp [IPRight, smulLeft]
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
        (TensorProduct.lift (IPRight (x + y) g)) z =
        (TensorProduct.lift (IPRight x g)) z + (TensorProduct.lift (IPRight y g)) z)
    aesop
    {
      simp [IPRight, distrLeft]
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
        star ((TensorProduct.lift (IPRight (m • x) g)) z) =
        m * star ((TensorProduct.lift (IPRight x g)) z))
    aesop
    {
      simp [IPRight]
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

private lemma IPLeftLin(M N: Type)
  [AddCommMonoid M][modM: Module ℂ M][ipM: IP M]
  [AddCommMonoid N][modN: Module ℂ N][ipN: IP N]
  (x y: M ⊗[ℂ] N): IPLeft (x+y) = IPLeft x + IPLeft y := by
  simp [IPLeft]
  ext a b
  simp

private lemma IPLeftLin2(M N: Type)
  [AddCommMonoid M][modM: Module ℂ M][ipM: IP M]
  [AddCommMonoid N][modN: Module ℂ N][ipN: IP N]
  (x: M ⊗[ℂ] N)(c: ℂ): IPLeft (c•x) = (star c)•IPLeft x := by
  ext g t
  simp [IPLeft]

-- TPAux is "Tensor Product Auxiliary"
private lemma TPAux{M : Type}
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

private lemma TPAux2{M : Type}
         {N : Type}
         {P : Type}
         [inst_1 : AddCommMonoid M]
         [inst_2 : AddCommMonoid N]
         [inst_3 : AddCommMonoid P]
         [inst_4 : Module ℂ M]
         [inst_5 : Module ℂ N]
         [inst_6 : Module ℂ P]
         (m1: M →ₗ[ℂ] N →ₗ[ℂ] P)
         (c: ℂ):
  TensorProduct.lift (c•m1) =
  c•TensorProduct.lift m1 := by
  aesop

private lemma TPComm(T₁ T₂: Type)
  [AddCommMonoid T₁][modM: Module ℂ T₁][ipM: IP T₁]
  [AddCommMonoid T₂][modN: Module ℂ T₂][ipN: IP T₂]:
∀v w : T₁ ⊗[ℂ] T₂,
star ((TensorProduct.lift (IPLeft w)) v) = star (star ((TensorProduct.lift (IPLeft v)) w)) := by
  intro v w
  rw [ComplexUtil.DoubleStar]
  apply Eq.symm

  let pr(x y: T₁ ⊗[ℂ] T₂):Prop:=
      (TensorProduct.lift (IPLeft x)) y = star ((TensorProduct.lift (IPLeft y)) x)
  have lem(x y: T₁ ⊗[ℂ] T₂): pr x y ↔ pr y x := by
    aesop
  have lem2(x y z: T₁ ⊗[ℂ] T₂): (pr x y ∧ pr x z) → pr x (y+z)  := by
    simp [pr, IPLeftLin]
    rw [TPAux]
    aesop
  have lem3(x y z: T₁ ⊗[ℂ] T₂): (pr x z ∧ pr y z) → pr (x+y) z  := by
    simp [pr, IPLeftLin]
    rw [TPAux]
    aesop

  have fol: pr v w → (TensorProduct.lift (IPLeft v)) w = star ((TensorProduct.lift (IPLeft w)) v) := by
    aesop
  apply fol
  clear fol
  apply TensorProduct.induction_on
      (motive := fun x:T₁ ⊗[ℂ] T₂ => pr x w)
  apply TensorProduct.induction_on
      (motive := fun y:T₁ ⊗[ℂ] T₂ => pr 0 y)
  aesop
  simp [pr, IPLeft]
  aesop
  apply TensorProduct.induction_on
      (motive := fun z:T₁ ⊗[ℂ] T₂ => ∀ (x : T₁) (y : T₂), pr (x ⊗ₜ[ℂ] y) z)
  simp [pr, IPLeft]
  {
    simp [pr, IPLeft, IPRight]
    intro x y x₁ y₁
    rw [IP.comm]
    rw [IP.comm y y₁]
    simp
  }
  {
    intro a b
    intro h₁ h₂
    intro c d
    apply lem2
    apply And.intro
    apply h₁
    apply h₂
  }
  apply TensorProduct.induction_on
      (motive := fun z:T₁ ⊗[ℂ] T₂ => ∀ (x y : T₁ ⊗[ℂ] T₂), pr x z → pr y z → pr (x + y) z)
  {
    intro a b
    intro h₁ h₂
    apply lem3
    aesop
  }
  {
    intro a b c d
    intro h₁ h₂
    apply lem3
    aesop
  }
  {
    intro a b
    intro h₁ h₂
    intro c d
    intro h₃ h₄
    apply lem3
    aesop
  }

-- This instance is inner product of tensor product of 2
-- vector spaces with inner product.
-- The idea behind this instance is the following:
-- With this instance we have only to define inner product
-- for basic types. Inner product for their tensor product
-- (and tensor product of tensor product and so on) is defined
-- automatically.
noncomputable
instance tensorProductIP(T₁ T₂: Type)
  [AddCommMonoid T₁][modM: Module ℂ T₁][ipM: IP T₁]
  [AddCommMonoid T₂][modN: Module ℂ T₂][ipN: IP T₂]:
  IP (T₁ ⊗[ℂ] T₂) :=
{
  -- inp mean "input"
  f(inp1 inp2: (T₁ ⊗[ℂ] T₂)) :=
    star (TensorProduct.lift (IPLeft inp2) inp1)
  comm := by
    apply TPComm T₁ T₂
  distrRight := by
    intro v w₁ w₂
    rw [ComplexUtil.DistrInvSumStar]
    rw [ComplexUtil.EqStar]
    rw [IPLeftLin]
    rw [TPAux]
    aesop
  smulRight := by
    intro v w m
    rw [IPLeftLin2]
    rw [TPAux2]
    simp
  self := by
    intro v
    apply TensorProduct.induction_on
        (motive := fun z:T₁ ⊗[ℂ] T₂ => (star ((TensorProduct.lift (IPLeft z)) z)).im = 0)
    {
      simp [IPLeft, IPRight]
    }
    {
      intro a b
      simp [IPLeft, IPRight]
      simp [ipN.self, ipM.self]
    }
    {
      intro x y
      intro hx hy
      simp [IPLeftLin, IPLeftLin2]
      simp [TPAux]
      simp at hx hy
      simp [hx, hy]
      have eq: ((TensorProduct.lift (IPLeft y)) x) = star ((TensorProduct.lift (IPLeft x)) y) := by
        let pr := TPComm T₁ T₂ y x
        simp [ComplexUtil.DoubleStar] at pr
        let pr_ := Eq.symm pr
        rw [ComplexUtil.Aux] at pr_
        apply pr_
      simp [eq]
    }
}

-- This class implements the following idea:
-- If we have two linearly isomorphic types and one of them
-- has inner product, we can "transfer" inner product from one
-- type to the other. However, the user can control this
-- trasferral by instantiating (or not instantiating) this class.
class Transfer(T: Type)
              [AddCommMonoid T][Module ℂ T]
  where
  TB : Type
  instMon: AddCommMonoid TB
  instMod: Module ℂ TB
  instIP: IP TB
  lE: T ≃ₗ[ℂ] TB

noncomputable
instance transferIP(T: Type)
         [AddCommMonoid T][Module ℂ T]
         [tr: Transfer T]:
         IP T :=
{
  f(a b: T) :=
    @IP.f tr.TB tr.instMon tr.instMod tr.instIP (tr.lE a) (tr.lE b)
  comm := by
    intro v w
    simp
    generalize r1: Transfer.lE v = v₁
    generalize rw: Transfer.lE w = w₁
    apply @IP.comm tr.TB tr.instMon tr.instMod tr.instIP v₁ w₁
  distrRight := by
    intro v w₁ w₂
    rw [@LinearEquiv.map_add ℂ ℂ T tr.TB _ _ _ tr.instMon _ tr.instMod _ _ _ _ tr.lE w₁ w₂]
    rw [@IP.distrRight tr.TB tr.instMon tr.instMod tr.instIP (tr.lE v) (tr.lE w₁) (tr.lE w₂)]
  smulRight := by
    intro v w m
    rw [@LinearEquiv.map_smul ℂ T tr.TB _ _ tr.instMon _ tr.instMod tr.lE m w]
    rw [@IP.smulRight tr.TB tr.instMon tr.instMod tr.instIP (tr.lE v) (tr.lE w) m]
  self := by
    intro v
    generalize r: Transfer.lE v = w
    apply tr.instIP.self w
}
