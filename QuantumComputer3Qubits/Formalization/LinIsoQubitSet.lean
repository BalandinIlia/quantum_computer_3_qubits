import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import QuantumComputer3Qubits.Formalization.QubitBasic
import QuantumComputer3Qubits.Formalization.QubitIndexed
import QuantumComputer3Qubits.Formalization.QubitSet

open scoped TensorProduct

lemma eq1(i1 i2: Fin 3)(neq: (i1 < i2)): (QubitSet1 i1) ⊗[ℂ] (QubitSet1 i2) = QubitSet2 i1 i2 neq := by
  simp

noncomputable
def isoImpl1(i1 i2: Fin 3):QubitSet1 i1 ⊗[ℂ] QubitSet1 i2 ≃ QubitSet1 i2 ⊗[ℂ] QubitSet1 i1 := TensorProduct.comm ℂ (QubitSet1 i1) (QubitSet1 i2)
noncomputable
def iso1(i1 i2: Fin 3)(neq: (i1 > i2)):(QubitSet2 i2 i1 (by aesop))≃(QubitSet1 i1 ⊗[ℂ] QubitSet1 i2):=isoImpl1 i2 i1

noncomputable
def iso2(i1 i2: Fin 3)(neq: (i1 < i2))(i3: Fin 3)(neq2: ¬(i3=i1))(neq3: ¬(i3=i2)):
  (QubitSet2 i1 i2 neq) ⊗[ℂ] (QubitSet1 i3) ≃ₗ[ℂ] QubitSet3 :=
  match i1, i2, i3 with
  | 0, 0, 0 => by aesop
  | 0, 0, 1 => by
    apply False.elim
    aesop
  | 0, 0, 2 => by
    apply False.elim
    aesop
  | 0, 1, 0 => by aesop
  | 0, 1, 1 => by aesop
  | 0, 1, 2 => by aesop
  | 0, 2, 0 => by
    apply False.elim
    aesop
  | 0, 2, 1 => by
    clear i1 i2 i3
    clear neq2 neq3
    simp [QubitSet2, QubitSet1, QubitSet3]
    clear neq
    simp [QubitIndMonoid, QubitIndModule, inferInstance]

    let Ts:Type := (QubitInd 0 ⊗[ℂ] QubitInd 2) ⊗[ℂ] QubitInd 1
    let Tf:Type := (QubitInd 0 ⊗[ℂ] QubitInd 1) ⊗[ℂ] QubitInd 2
    let T1:Type := QubitInd 0 ⊗[ℂ] (QubitInd 2 ⊗[ℂ] QubitInd 1)
    let T2:Type := QubitInd 0 ⊗[ℂ] (QubitInd 1 ⊗[ℂ] QubitInd 2)

    have iso1: Ts ≃ₗ[ℂ] T1 := by
      simp [Ts, T1]
      exact TensorProduct.assoc ℂ (QubitInd 0) (QubitInd 2) (QubitInd 1)
    have iso2: T1 ≃ₗ[ℂ] T2 := by
      simp [T1, T2]
      let i1:QubitInd 2 ⊗[ℂ] QubitInd 1 ≃ₗ[ℂ] QubitInd 1 ⊗[ℂ] QubitInd 2 :=
        TensorProduct.comm ℂ (QubitInd 2) (QubitInd 1)
      let i2 := LinearEquiv.refl ℂ (QubitInd 0)
      let i3 := TensorProduct.congr i2 i1
      exact i3
    have iso3: T2 ≃ₗ[ℂ] Tf := by
      let i:=TensorProduct.assoc ℂ (QubitInd 0) (QubitInd 1) (QubitInd 2)
      simp [T2, Tf]
      exact (LinearEquiv.symm i)
    have isoComp1: Ts ≃ₗ[ℂ] T2 := LinearEquiv.trans iso1 iso2
    have isoFin: Ts ≃ₗ[ℂ] Tf := LinearEquiv.trans isoComp1 iso3
    clear iso1 iso2 iso3 isoComp1 T1 T2

    exact isoFin
  | 0, 2, 2 => by aesop
  | 1, 0, 0 => by aesop
  | 1, 0, 1 => by aesop
  | 1, 0, 2 => by
    apply False.elim
    aesop
  | 1, 1, 0 => by
    apply False.elim
    aesop
  | 1, 1, 1 => by aesop
  | 1, 1, 2 => by
    apply False.elim
    aesop
  | 1, 2, 0 => by
    clear i1 i2 i3 neq2 neq3
    simp [QubitSet2, QubitSet1, QubitSet3]
    clear neq
    simp [QubitIndMonoid, QubitIndModule, inferInstance]

    let Ts:Type := (QubitInd 1 ⊗[ℂ] QubitInd 2) ⊗[ℂ] (QubitInd 0)
    let Tf:Type := (QubitInd 0 ⊗[ℂ] QubitInd 1) ⊗[ℂ] (QubitInd 2)
    let T1:Type := (QubitInd 2 ⊗[ℂ] QubitInd 1) ⊗[ℂ] (QubitInd 0)
    let T2:Type := (QubitInd 2) ⊗[ℂ] (QubitInd 1 ⊗[ℂ] QubitInd 0)
    let T3:Type := (QubitInd 2) ⊗[ℂ] (QubitInd 0 ⊗[ℂ] QubitInd 1)

    have iso1: Ts ≃ₗ[ℂ] T1 := by
      simp [Ts, T1]
      let i1:QubitInd 1 ⊗[ℂ] QubitInd 2 ≃ₗ[ℂ] QubitInd 2 ⊗[ℂ] QubitInd 1 :=
        TensorProduct.comm ℂ (QubitInd 1) (QubitInd 2)
      let i2 := LinearEquiv.refl ℂ (QubitInd 0)
      let i3 := TensorProduct.congr i1 i2
      exact i3
    have iso2: T1 ≃ₗ[ℂ] T2 := by
      simp [T1, T2]
      let i:=TensorProduct.assoc ℂ (QubitInd 2) (QubitInd 1) (QubitInd 0)
      exact i
    have iso3: T2 ≃ₗ[ℂ] T3 := by
      simp [T2, T3]
      let i1:QubitInd 1 ⊗[ℂ] QubitInd 0 ≃ₗ[ℂ] QubitInd 0 ⊗[ℂ] QubitInd 1 :=
        TensorProduct.comm ℂ (QubitInd 1) (QubitInd 0)
      let i2 := LinearEquiv.refl ℂ (QubitInd 2)
      let i3 := TensorProduct.congr i2 i1
      exact i3
    have iso4: T3 ≃ₗ[ℂ] Tf := by
      simp [T3, Tf]
      let i1:QubitInd 2 ⊗[ℂ] (QubitInd 0 ⊗[ℂ] QubitInd 1) ≃ₗ[ℂ] (QubitInd 0 ⊗[ℂ] QubitInd 1) ⊗[ℂ] QubitInd 2 :=
        TensorProduct.comm ℂ (QubitInd 2) (QubitInd 0 ⊗[ℂ] QubitInd 1)
      exact i1

    have isoComp1: Ts ≃ₗ[ℂ] T2 := LinearEquiv.trans iso1 iso2
    have isoComp2: Ts ≃ₗ[ℂ] T3 := LinearEquiv.trans isoComp1 iso3
    have isoFin: Ts ≃ₗ[ℂ] Tf := LinearEquiv.trans isoComp2 iso4
    exact isoFin
  | 1, 2, 1 => by aesop
  | 1, 2, 2 => by aesop
  | 2, 0, 0 => by aesop
  | 2, 0, 1 => by
    apply False.elim
    aesop
  | 2, 0, 2 => by
    apply False.elim
    aesop
  | 2, 1, 0 => by
    apply False.elim
    aesop
  | 2, 1, 1 => by aesop
  | 2, 1, 2 => by aesop
  | 2, 2, 0 => by
    apply False.elim
    aesop
  | 2, 2, 1 => by
    apply False.elim
    aesop
  | 2, 2, 2 => by aesop
