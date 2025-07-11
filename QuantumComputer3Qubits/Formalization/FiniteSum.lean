import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Complex.Basic
-- This file formalizes finite sum.
-- We found it extremely difficult to work with Mathlib
-- finsum and to prove even trivial properties of it, so we
-- decided to make our own finsum defition in order to have
-- complete control over it.

-- FS means "Finite Sum"
namespace FS

def sumPartial(T: Type)
              [AddCommMonoid T]
              (N: ℕ)
              (pos: N > 0)
              (F: Fin N → T)
              (M: Fin N): T :=
match M with
| (@Fin.mk N 0 ord) => F (@Fin.mk N 0 ord)
| (@Fin.mk N (Nat.succ m) ord) =>
      (sumPartial T N pos F (@Fin.mk N m (by omega))) +
      (F (@Fin.mk N (Nat.succ m) ord))

def fs{T: Type}
      [AddCommMonoid T]
      {N: ℕ}
      (F: Fin N → T):T :=
match N with
| 0 => 0
| Nat.succ K => sumPartial T (K+1) (by omega) F (@Fin.mk (K+1) K (by omega))

lemma applyMap {T: Type}
               [AddCommMonoid T]
               [Module ℂ T]
               {N: ℕ}
               (A: Fin N → (T →ₗ[ℂ] T))
               (x: T):
(fs A) x = fs (fun i: Fin N => A i x) := by
  simp [fs]
  cases N with
  | zero => simp
  | succ n =>
    simp
    let pr(m: ℕ)(ord: m < n + 1) :=
        sumPartial (T →ₗ[ℂ] T) (n + 1) (by omega) A (@Fin.mk (n+1) m ord) x =
        sumPartial T (n + 1) (by omega) (fun i => (A i) x) (@Fin.mk (n+1) m ord)
    have st(m: ℕ)(ord: m < n + 1): pr m ord := by
      induction m with
      | zero =>
        simp [pr]
        rw [sumPartial.eq_def]
        rw [sumPartial.eq_def]
        aesop
      | succ nn ih =>
        simp [pr]
        rw [sumPartial.eq_def]
        rw [sumPartial.eq_def]
        simp
        simp [pr] at ih
        simp [ih]
    have st_ := st n (by omega)
    simp [pr] at st_
    apply st_

lemma distrLeft {T: Type}
                [AddCommMonoid T]
                [Module ℂ T]
                {N: ℕ}
                (op: T → T → ℂ)
                (prop: ∀x1 x2 y: T, op (x1+x2) y = op x1 y + op x2 y)
                (prop2: ∀m: ℂ, ∀x y: T, op (m • x) y = m * (op x y))
                (S: Fin N → T)
                (x: T):
op (fs S) x = fs (fun i: Fin N => op (S i) x) := by
  simp [fs]
  cases N with
  | zero =>
    simp
    have eq: op ((0:ℂ) • x) x = (0:ℂ) * (op x x) := by
      apply prop2 (0:ℂ) x x
    simp at eq
    apply eq
  | succ n =>
    simp
    let pr(m: ℕ)(ord: m < n + 1) :=
        op (sumPartial T (n + 1) (by aesop) S (Fin.mk m (by omega))) x =
        sumPartial ℂ (n + 1) (by omega) (fun i => op (S i) x) (Fin.mk m (by omega))
    have st(m: ℕ)(ord: m < n + 1): pr m ord := by
      induction m with
      | zero =>
        simp [pr]
        rw [sumPartial.eq_def]
        rw [sumPartial.eq_def]
        aesop
      | succ nn ih =>
        simp [pr]
        rw [sumPartial.eq_def]
        rw [sumPartial.eq_def]
        simp [pr] at ih
        aesop
    have st_ := st n (by omega)
    simp [pr] at st_
    apply st_

lemma distrRight {T: Type}
                 [AddCommMonoid T]
                 [Module ℂ T]
                 {N: ℕ}
                 (op: T → T → ℂ)
                 (prop: ∀x y1 y2: T, op x (y1+y2) = op x y1 + op x y2)
                 (prop2: ∀m: ℂ, ∀x y: T, op x (m • y) = m * (op x y))
                 (S: Fin N → T)
                 (x: T):
op x (fs S) = fs (fun i: Fin N => op x (S i)) := by
  simp [fs]
  cases N with
  | zero =>
    simp
    have eq: op x ((0:ℂ) • x) = (0:ℂ) * (op x x) := by
      apply prop2 (0:ℂ) x x
    simp at eq
    apply eq
  | succ n =>
    simp
    let pr(m: ℕ)(ord: m < n + 1) :=
        op x (sumPartial T (n + 1) (by aesop) S (Fin.mk m (by omega))) =
        sumPartial ℂ (n + 1) (by omega) (fun i => op x (S i)) (Fin.mk m (by omega))
    have st(m: ℕ)(ord: m < n + 1): pr m ord := by
      induction m with
      | zero =>
        simp [pr]
        rw [sumPartial.eq_def]
        rw [sumPartial.eq_def]
        aesop
      | succ nn ih =>
        simp [pr]
        rw [sumPartial.eq_def]
        rw [sumPartial.eq_def]
        simp [pr] at ih
        aesop
    have st_ := st n (by omega)
    simp [pr] at st_
    apply st_

lemma applyDistr {T: Type}
                 [AddCommMonoid T]
                 [Module ℂ T]
                 {N: ℕ}
                 (A: (T →ₗ[ℂ] T))
                 (x: Fin N → T):
A (fs x) = fs (fun i: Fin N => A (x i)) := by
  simp [fs]
  cases N with
  | zero =>
    simp
  | succ n =>
    simp
    let pr(m: ℕ)(ord: m < n + 1) :=
        A (sumPartial T (n + 1) (by omega) x (Fin.mk m (by omega))) =
        sumPartial T (n + 1) (by omega) (fun i => A (x i)) (Fin.mk m (by omega))
    have st(m: ℕ)(ord: m < n + 1): pr m ord := by
      induction m with
      | zero =>
        simp [pr]
        rw [sumPartial.eq_def]
        rw [sumPartial.eq_def]
        aesop
      | succ nn ih =>
        simp [pr]
        rw [sumPartial.eq_def]
        rw [sumPartial.eq_def]
        simp [pr] at ih
        aesop
    have st_ := st n (by omega)
    simp [pr] at st_
    apply st_

lemma doubleFS {T: Type}
               [AddCommMonoid T]
               (N: ℕ)
               (pos: N > 0)
               (S: Fin N → Fin N → T):
fs (fun i: Fin N => fs (fun j: Fin N => if(i=j) then S j i else 0)) =
fs (fun i: Fin N => S i i) := by
  have lem: ∀i: Fin N, fs (fun j:Fin N => if i = j then S j i else 0) = S i i := by
    intro i
    simp [fs]
    cases N with
    | zero =>
      aesop
    | succ n =>
      simp
      let pr(m: ℕ)(ord: m < n + 1) :=
          sumPartial T (n + 1) (by omega) (fun j => if i = j then S j i else 0) (Fin.mk m (by omega)) =
          if m≥i then S i i else 0
      have st(m: ℕ)(ord: m < n + 1): pr m ord := by
        induction m with
        | zero =>
          simp [pr]
          rw [sumPartial.eq_def]
          aesop
        | succ nn ih =>
          simp [pr]
          rw [sumPartial.eq_def]
          simp
          simp [pr] at ih
          simp [ih]
          let A:Prop := i ≤ nn
          by_cases A
          case pos hh =>
            simp [A] at hh
            simp [hh]
            have t:↑i ≤ nn + 1 := by fin_omega
            simp [t]
            have r: ¬(i = Fin.mk (nn+1) (by omega)) := by
              aesop
            simp [r]
          case neg hh =>
            simp [A] at hh
            have t:¬(↑i ≤ nn) := by fin_omega
            simp [t]
            let B:Prop := i = Fin.mk (nn+1) (by omega)
            by_cases B
            case pos hhh =>
              simp [B] at hhh
              have t:(↑i ≤ nn + 1) := by aesop
              simp [t, hhh]
            case neg hhh =>
              simp [B] at hhh
              simp [hhh]
              intro ui
              apply False.elim
              clear ih A B t pr pos S
              have hj:↑i = nn + 1 := by
                clear hhh
                omega
              clear ui hh
              have io: i = Fin.mk i.val (by aesop) := by
                simp [Fin.mk]
              rw [io] at hhh
              simp [hj] at hhh
      have st_ := st n (by omega)
      simp [pr] at st_
      rw [st_]
      have r: ↑i ≤ n := by
        let st := @Fin.isLt (n+1) i
        apply @Nat.le_of_lt_succ _ n st
      simp [r]
  simp [lem]

-- this is property that any vector is equal to its
-- decomposition into basis vectors
def basisRepr (N: ℕ) -- linear space dimension
              (_: N > 0)
              (T: Type) -- linear space vector type
              [AddCommMonoid T]
              [Module ℂ T]
              (bas: Basis (Fin N) ℂ T) -- basis
              (x: T) := -- decomposed vector
  x = fs (fun i: Fin N => (Basis.repr bas x i) • (bas i))

-- Here we set an axiom that any vector is equal to its
-- decomposition into basis vectors
axiom basisReprAx {T: Type}
                  [AddCommMonoid T]
                  [Module ℂ T]
                  (N: ℕ)
                  (pos: N > 0)
                  (bas: Basis (Fin N) ℂ T)
                  (x: T):
  basisRepr N pos T bas x
