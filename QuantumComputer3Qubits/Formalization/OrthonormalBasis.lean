import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import QuantumComputer3Qubits.Formalization.InnerProduct

open scoped TensorProduct

class OrthonormalBasis(T: Type)[AddCommMonoid T]
                               [Module ℂ T]
                               [IP T] where
  N: ℕ
  basis: Basis (Fin N) ℂ T
  prop: ∀i j: Fin N, (IP.f (basis i) (basis j)) =
                           if i = j then 1 else 0

-- OB means "Orthonormal Basis"
namespace OB

class OrthonormalBasisImpl (T: Type)(N: ℕ) [AddCommMonoid T]
                                           [Module ℂ T]
                                           [IP T] where
  basis: Basis (Fin N) ℂ T
  prop: ∀i j: Fin N, (IP.f (basis i) (basis j)) =
                           if i = j then 1 else 0

noncomputable
def transferOrt(T: Type)(N: ℕ)
               {mon: AddCommMonoid T}
               {mod: Module ℂ T}
               {tr: IP.Transfer T}
               (ob: @OrthonormalBasisImpl
                    tr.TB
                    N
                    tr.instMon
                    tr.instMod
                    tr.instIP):
OrthonormalBasisImpl T N :=
{
  basis := @Basis.map (Fin N) ℂ tr.TB T _ tr.instMon tr.instMod _ _ ob.basis
           (@LinearEquiv.symm ℂ ℂ T tr.TB _ _ _ tr.instMon _ tr.instMod _ _ _ _ tr.lE)
  prop := by
    simp
    intro i j
    have eq: ∀v w: tr.TB, IP.f ((@LinearEquiv.symm ℂ ℂ T tr.TB _ _ _ tr.instMon _ tr.instMod _ _ _ _ tr.lE) v) ((@LinearEquiv.symm ℂ ℂ T tr.TB _ _ _ tr.instMon _ tr.instMod _ _ _ _ tr.lE) w) = @IP.f tr.TB tr.instMon tr.instMod tr.instIP v w := by
      intro v w
      simp [IP.f]
    simp [eq]
    simp [ob.prop]
}

def rebase_2_2: Fin 2 × Fin 2 ≃ Fin 4 :=
{
  toFun := by
    intro arg
    let (a1, a2) := arg
    match a1, a2 with
    | 0, 0 => exact @Fin.mk 4 0 (by aesop)
    | 0, 1 => exact @Fin.mk 4 1 (by aesop)
    | 1, 0 => exact @Fin.mk 4 2 (by aesop)
    | 1, 1 => exact @Fin.mk 4 3 (by aesop)
  invFun := by
    intro arg
    match arg with
    | 0 => exact (@Fin.mk 2 0 (by aesop), @Fin.mk 2 0 (by aesop))
    | 1 => exact (@Fin.mk 2 0 (by aesop), @Fin.mk 2 1 (by aesop))
    | 2 => exact (@Fin.mk 2 1 (by aesop), @Fin.mk 2 0 (by aesop))
    | 3 => exact (@Fin.mk 2 1 (by aesop), @Fin.mk 2 1 (by aesop))
  left_inv := by
    simp [Function.LeftInverse]
    intro a b
    all_goals fin_cases a
    all_goals fin_cases b
    all_goals simp
  right_inv := by
    simp [Function.LeftInverse]
    intro a
    all_goals fin_cases a
    all_goals simp
}

def rebase_4_2: Fin 4 × Fin 2 ≃ Fin 8 :=
{
  toFun := by
    intro arg
    let (a1, a2) := arg
    match a1, a2 with
    | 0, 0 => exact @Fin.mk 8 0 (by aesop)
    | 0, 1 => exact @Fin.mk 8 1 (by aesop)
    | 1, 0 => exact @Fin.mk 8 2 (by aesop)
    | 1, 1 => exact @Fin.mk 8 3 (by aesop)
    | 2, 0 => exact @Fin.mk 8 4 (by aesop)
    | 2, 1 => exact @Fin.mk 8 5 (by aesop)
    | 3, 0 => exact @Fin.mk 8 6 (by aesop)
    | 3, 1 => exact @Fin.mk 8 7 (by aesop)
  invFun := by
    intro arg
    match arg with
    | 0 => exact (@Fin.mk 4 0 (by aesop), @Fin.mk 2 0 (by aesop))
    | 1 => exact (@Fin.mk 4 0 (by aesop), @Fin.mk 2 1 (by aesop))
    | 2 => exact (@Fin.mk 4 1 (by aesop), @Fin.mk 2 0 (by aesop))
    | 3 => exact (@Fin.mk 4 1 (by aesop), @Fin.mk 2 1 (by aesop))
    | 4 => exact (@Fin.mk 4 2 (by aesop), @Fin.mk 2 0 (by aesop))
    | 5 => exact (@Fin.mk 4 2 (by aesop), @Fin.mk 2 1 (by aesop))
    | 6 => exact (@Fin.mk 4 3 (by aesop), @Fin.mk 2 0 (by aesop))
    | 7 => exact (@Fin.mk 4 3 (by aesop), @Fin.mk 2 1 (by aesop))
  left_inv := by
    simp [Function.LeftInverse]
    intro a b
    all_goals fin_cases a
    all_goals fin_cases b
    all_goals simp
  right_inv := by
    simp [Function.LeftInverse]
    intro a
    all_goals fin_cases a
    all_goals simp
}

def rebase_2_4: Fin 2 × Fin 4 ≃ Fin 8 :=
{
  toFun := by
    intro arg
    let (a1, a2) := arg
    match a1, a2 with
    | 0, 0 => exact @Fin.mk 8 0 (by aesop)
    | 0, 1 => exact @Fin.mk 8 1 (by aesop)
    | 0, 2 => exact @Fin.mk 8 2 (by aesop)
    | 0, 3 => exact @Fin.mk 8 3 (by aesop)
    | 1, 0 => exact @Fin.mk 8 4 (by aesop)
    | 1, 1 => exact @Fin.mk 8 5 (by aesop)
    | 1, 2 => exact @Fin.mk 8 6 (by aesop)
    | 1, 3 => exact @Fin.mk 8 7 (by aesop)
  invFun := by
    intro arg
    match arg with
    | 0 => exact (@Fin.mk 2 0 (by aesop), @Fin.mk 4 0 (by aesop))
    | 1 => exact (@Fin.mk 2 0 (by aesop), @Fin.mk 4 1 (by aesop))
    | 2 => exact (@Fin.mk 2 0 (by aesop), @Fin.mk 4 2 (by aesop))
    | 3 => exact (@Fin.mk 2 0 (by aesop), @Fin.mk 4 3 (by aesop))
    | 4 => exact (@Fin.mk 2 1 (by aesop), @Fin.mk 4 0 (by aesop))
    | 5 => exact (@Fin.mk 2 1 (by aesop), @Fin.mk 4 1 (by aesop))
    | 6 => exact (@Fin.mk 2 1 (by aesop), @Fin.mk 4 2 (by aesop))
    | 7 => exact (@Fin.mk 2 1 (by aesop), @Fin.mk 4 3 (by aesop))
  left_inv := by
    simp [Function.LeftInverse]
    intro a b
    all_goals fin_cases a
    all_goals fin_cases b
    all_goals simp
  right_inv := by
    simp [Function.LeftInverse]
    intro a
    all_goals fin_cases a
    all_goals simp
}

noncomputable
instance tp_2_2(T1 T2: Type)
               [mon1: AddCommMonoid T1]
               [mod1: Module ℂ T1]
               [ip1: IP T1]
               [ob1: OrthonormalBasisImpl T1 2]
               [mon2: AddCommMonoid T2]
               [mod2: Module ℂ T2]
               [ip2: IP T2]
               [ob2: OrthonormalBasisImpl T2 2]:
OrthonormalBasisImpl (T1 ⊗[ℂ] T2) 4 :=
{
  basis := Basis.reindex
           (Basis.tensorProduct ob1.basis ob2.basis)
           rebase_2_2
  prop := by
    intro i j
    all_goals fin_cases i
    all_goals fin_cases j
    all_goals simp [IP.f, IP.IPLeft, rebase_2_2, IP.IPRight]
    all_goals simp [ob1.prop, ob2.prop]
}

set_option maxHeartbeats 1000000

noncomputable
instance tp_4_2(T1 T2: Type)
               [mon1: AddCommMonoid T1]
               [mod1: Module ℂ T1]
               [ip1: IP T1]
               [ob1: OrthonormalBasisImpl T1 4]
               [mon2: AddCommMonoid T2]
               [mod2: Module ℂ T2]
               [ip2: IP T2]
               [ob2: OrthonormalBasisImpl T2 2]:
OrthonormalBasisImpl (T1 ⊗[ℂ] T2) 8 :=
{
  basis := Basis.reindex
           (Basis.tensorProduct ob1.basis ob2.basis)
           rebase_4_2
  prop := by
    intro i j
    all_goals fin_cases i
    all_goals fin_cases j
    all_goals simp [IP.f, IP.IPLeft, rebase_4_2, IP.IPRight]
    all_goals simp [ob1.prop, ob2.prop]
}

noncomputable
instance tp_2_4(T1 T2: Type)
               [mon1: AddCommMonoid T1]
               [mod1: Module ℂ T1]
               [ip1: IP T1]
               [ob1: OrthonormalBasisImpl T1 2]
               [mon2: AddCommMonoid T2]
               [mod2: Module ℂ T2]
               [ip2: IP T2]
               [ob2: OrthonormalBasisImpl T2 4]:
OrthonormalBasisImpl (T1 ⊗[ℂ] T2) 8 :=
{
  basis := Basis.reindex
           (Basis.tensorProduct ob1.basis ob2.basis)
           rebase_2_4
  prop := by
    intro i j
    all_goals fin_cases i
    all_goals fin_cases j
    all_goals simp [IP.f, IP.IPLeft, rebase_2_4, IP.IPRight]
    all_goals simp [ob1.prop, ob2.prop]
}

class Dimensional(T: Type) where dim:ℕ

instance transferDim(T: Type)
                    [AddCommMonoid T]
                    [Module ℂ T]
                    [IP.Transfer T]
                    [d: Dimensional T]:
Dimensional T:=
{
  dim := d.dim
}

noncomputable
instance tp_dim(T1 T2: Type)
               [AddCommMonoid T1]
               [Module ℂ T1]
               [IP T1]
               [d1: Dimensional T1]
               [AddCommMonoid T2]
               [Module ℂ T2]
               [IP T2]
               [d2: Dimensional T2]:
Dimensional (T1 ⊗[ℂ] T2) :=
{
  dim := d1.dim * d2.dim
}

noncomputable
instance OrthonormalBasisInstDim2(T: Type)
                                 [AddCommMonoid T]
                                 [Module ℂ T]
                                 [IP T]
                                 [impl: OrthonormalBasisImpl T 2]:
                                 OrthonormalBasis T :=
{
  N := 2
  basis := impl.basis
  prop := by
    intro i j
    simp [impl.prop]
}

noncomputable
instance OrthonormalBasisInstDim4(T: Type)
                                 [AddCommMonoid T]
                                 [Module ℂ T]
                                 [IP T]
                                 [impl: OrthonormalBasisImpl T 4]:
                                 OrthonormalBasis T :=
{
  N := 4
  basis := impl.basis
  prop := by
    intro i j
    simp [impl.prop]
}

noncomputable
instance OrthonormalBasisInstDim8(T: Type)
                                 [AddCommMonoid T]
                                 [Module ℂ T]
                                 [IP T]
                                 [impl: OrthonormalBasisImpl T 8]:
                                 OrthonormalBasis T :=
{
  N := 8
  basis := impl.basis
  prop := by
    intro i j
    simp [impl.prop]
}
