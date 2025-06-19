import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import QuantumComputer3Qubits.QubitBasic
import QuantumComputer3Qubits.QubitIndexed

open scoped TensorProduct

@[reducible]
def QubitSet1(i1: Fin 3):Type := QubitInd i1
#synth Module ℂ (QubitSet1 1)

@[reducible]
def QubitSet2(i1 i2: Fin 3)(neq: (i1 < i2)):Type := (QubitInd i1) ⊗[ℂ] (QubitInd i2)

@[reducible]
def QubitSet3Impl(t: Fin 3):Type := (QubitSet2 0 1 (by simp)) ⊗[ℂ] (QubitInd t)
@[reducible]
def QubitSet3:Type := QubitSet3Impl 2

lemma eq1(i1 i2: Fin 3)(neq: (i1 < i2)): (QubitSet1 i1) ⊗[ℂ] (QubitSet1 i2) = QubitSet2 i1 i2 neq := by
  simp

noncomputable
def isoImpl1(i1 i2: Fin 3):QubitSet1 i1 ⊗[ℂ] QubitSet1 i2 ≃ QubitSet1 i2 ⊗[ℂ] QubitSet1 i1 := TensorProduct.comm ℂ (QubitSet1 i1) (QubitSet1 i2)
noncomputable
def iso1(i1 i2: Fin 3)(neq: (i1 > i2)):(QubitSet2 i2 i1 (by aesop))≃(QubitSet1 i1 ⊗[ℂ] QubitSet1 i2):=isoImpl1 i2 i1

noncomputable
def iso2(i1 i2: Fin 3)(neq: (i1 < i2))(i3: Fin 3)(neq2: ¬(i1=i3))(neq3: ¬(i1=i2)):
  (QubitSet2 i1 i2 neq) ⊗[ℂ] (QubitSet1 i3) ≃ QubitSet3 :=
  match i1, i2, i3 with
  | 0, 2, 1 => by
    clear i1 i2 i3
    clear neq2 neq3
    simp [QubitSet2, QubitSet1]
    clear neq
    simp [QubitSet3, QubitSet3Impl]
    simp [QubitSet2]

    let Ts:Type :=
      @TensorProduct ℂ _
                    (@TensorProduct ℂ _ (QubitInd 0) (QubitInd 2) (QubitIndMonoid 0) (QubitIndMonoid 2) (QubitIndModule 0) (QubitIndModule 2))
                    (QubitInd 1) _ (QubitIndMonoid 1) _ (QubitIndModule 1)
    let Tf:Type :=
      @TensorProduct ℂ _
                    (@TensorProduct ℂ _ (QubitInd 0) (QubitInd 1) (QubitIndMonoid 0) (QubitIndMonoid 1) (QubitIndModule 0) (QubitIndModule 1))
                    (QubitInd 2) _ (QubitIndMonoid 2) _ (QubitIndModule 2)
    let T1:Type :=
      @TensorProduct ℂ _ (QubitInd 0)
      (@TensorProduct ℂ _ (QubitInd 2) (QubitInd 1) (QubitIndMonoid 2) (QubitIndMonoid 1) (QubitIndModule 2) (QubitIndModule 1))
      (QubitIndMonoid 0) _ (QubitIndModule 0) _
    let T2:Type :=
      @TensorProduct ℂ _ (QubitInd 0)
      (@TensorProduct ℂ _ (QubitInd 1) (QubitInd 2) (QubitIndMonoid 1) (QubitIndMonoid 2) (QubitIndModule 1) (QubitIndModule 2))
      (QubitIndMonoid 0) _ (QubitIndModule 0) _

    have iso1: Ts ≃ₗ[ℂ] T1 := by
      simp [Ts, T1]
      exact @TensorProduct.assoc ℂ _ (QubitInd 0) (QubitInd 2) (QubitInd 1) (QubitIndMonoid 0) (QubitIndMonoid 2) (QubitIndMonoid 1) (QubitIndModule 0) (QubitIndModule 2) (QubitIndModule 1)
    have iso2: T1 ≃ₗ[ℂ] T2 := by
      simp [T1, T2]
      let Tl:Type := (@TensorProduct ℂ _ (QubitInd 2) (QubitInd 1) (QubitIndMonoid 2) (QubitIndMonoid 1) (QubitIndModule 2) (QubitIndModule 1))
      let Tr:Type := (@TensorProduct ℂ _ (QubitInd 1) (QubitInd 2) (QubitIndMonoid 1) (QubitIndMonoid 2) (QubitIndModule 1) (QubitIndModule 2))
      let i1:Tl ≃ₗ[ℂ] Tr :=
        @TensorProduct.comm ℂ _ (QubitInd 2) (QubitInd 1) (QubitIndMonoid 2) (QubitIndMonoid 1) (QubitIndModule 2) (QubitIndModule 1)
      let i2 := @LinearEquiv.refl ℂ (QubitInd 0) _ (QubitIndMonoid 0) (QubitIndModule 0)
      let i3 := @TensorProduct.congr ℂ _ (QubitInd 0) Tl (QubitInd 0) Tr (QubitIndMonoid 0) _ (QubitIndMonoid 0) _ (QubitIndModule 0) _ _ (QubitIndModule 0) i2 i1
      simp [Tl, Tr] at i3
      exact i3
    have iso3: T2 ≃ₗ[ℂ] Tf := by
      let i:=
        @TensorProduct.assoc ℂ _ (QubitInd 0) (QubitInd 1) (QubitInd 2) (QubitIndMonoid 0) (QubitIndMonoid 1) (QubitIndMonoid 2) (QubitIndModule 0) (QubitIndModule 1) (QubitIndModule 2)
      simp [T2, Tf]
      exact (LinearEquiv.symm i)
    have isoComp1: Ts ≃ₗ[ℂ] T2 := LinearEquiv.trans iso1 iso2
    have isoFin: Ts ≃ₗ[ℂ] Tf := LinearEquiv.trans isoComp1 iso3
    clear iso1 iso2 iso3 isoComp1 T1 T2

    let t:Ts ≃ Tf := isoFin
    simp [Ts, Tf] at t
    exact t
  | _, _, _ => sorry
