import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Complex.Basic
-- This file formalizes finite sum.
-- We found it extremely difficult to work with Mathlib
-- finsum and to prove even trivial properties of it, so we
-- decided to make our own finsum defition in order to have
-- complete control over it.

-- FS means "Finite Sum"
namespace FS

-- This function defines partial sum:
-- We have N values of type T (represented with function
-- Fin N → T below).
-- We calculate sum of all values until M-th value.
-- This function is used as implementation of finite sum.
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

-- fs means "finite sum"
-- fs defines sum of N values
def fs{T: Type}
      [AddCommMonoid T]
      {N: ℕ}
      (F: Fin N → T):T :=
match N with
| 0 => 0
| Nat.succ K => sumPartial T (K+1) (by omega) F (@Fin.mk (K+1) K (by omega))

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
-- decomposition into basis vectors.
-- This is a very fragile part of the project (since it is
-- an axiom, it does not have any proof), so it is
-- carefully tested: basisRepr is proven for all N values
-- from 1 to 6.
axiom basisReprAx {T: Type}
                  [AddCommMonoid T]
                  [Module ℂ T]
                  (N: ℕ)
                  (pos: N > 0)
                  (bas: Basis (Fin N) ℂ T)
                  (x: T):
  basisRepr N pos T bas x

lemma FS8{T: Type}
         [AddCommMonoid T]
         (F: Fin 8 → T):
  FS.fs F = F 0 + F 1 + F 2 + F 3 + F 4 + F 5 + F 6 + F 7 := by
  simp [FS.fs, FS.sumPartial.eq_def]

lemma FS8_rev{T: Type}
             [AddCommMonoid T]
             (f1 f2 f3 f4 f5 f6 f7 f8: T):
f1 + f2 + f3 + f4 + f5 + f6 + f7 + f8 =
FS.fs (fun i: Fin 8 => match i with
            | 0 => f1
            | 1 => f2
            | 2 => f3
            | 3 => f4
            | 4 => f5
            | 5 => f6
            | 6 => f7
            | 7 => f8
      )  := by
  simp [FS.fs, FS.sumPartial.eq_def]

lemma FS4{T: Type}
         [AddCommMonoid T]
         (F: Fin 4 → T):
  FS.fs F = F 0 + F 1 + F 2 + F 3 := by
  simp [FS.fs, FS.sumPartial.eq_def]

lemma FS4_rev{T: Type}
             [AddCommMonoid T]
             (f1 f2 f3 f4: T):
f1 + f2 + f3 + f4 =
FS.fs (fun i: Fin 4 => match i with
            | 0 => f1
            | 1 => f2
            | 2 => f3
            | 3 => f4
      )  := by
  simp [FS.fs, FS.sumPartial.eq_def]

lemma FS2{T: Type}
         [AddCommMonoid T]
         (F: Fin 2 → T):
  FS.fs F = F 0 + F 1 := by
  simp [FS.fs, FS.sumPartial.eq_def]

lemma FS2_rev{T: Type}
             [AddCommMonoid T]
             (f1 f2: T):
f1 + f2 =
FS.fs (fun i: Fin 2 => match i with
            | 0 => f1
            | 1 => f2
      )  := by
  simp [FS.fs, FS.sumPartial.eq_def]

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
                (prop2: ∀m: ℂ, ∀x y: T, op (m • x) y = (star m) * (op x y))
                (S: Fin N → T)
                (x: T):
op (fs S) x = fs (fun i: Fin N => op (S i) x) := by
  simp [fs]
  cases N with
  | zero =>
    simp
    have eq: op ((0:ℂ) • x) x = star (0:ℂ) * (op x x) := by
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

lemma Kronecker {T: Type}
                [AddCommMonoid T]
                (N: ℕ)
                (pos: N > 0)
                (ind: Fin N)
                (F: Fin N → T):
fs (fun i:Fin N => if (ind=i) then F i else 0) = F ind := by
  cases N with
    | zero =>
      aesop
    | succ n =>
      simp [fs]
      clear pos
      let pr(m: ℕ)(ord: m < n + 1) :=
          sumPartial T
                     (n + 1)
                     (by omega)
                     (fun i:Fin (n+1) =>
                          if (ind=i) then F i else 0)
                     (@Fin.mk (n+1) m ord) =
          if m ≥ ind then F ind else 0
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
          clear ih pr
          let A:Prop := ind ≤ nn
          by_cases A
          case pos hh =>
            simp [A] at hh
            simp [hh]
            have t:↑ind ≤ nn + 1 := by fin_omega
            simp [t]
            have r: ¬(ind = Fin.mk (nn+1) (by omega)) := by
              aesop
            simp [r]
          case neg hh =>
            simp [A] at hh
            have t:¬(↑ind ≤ nn) := by fin_omega
            simp [t]
            let B:Prop := ind = Fin.mk (nn+1) (by omega)
            by_cases B
            case pos hhh =>
              simp [B] at hhh
              have t:(↑ind ≤ nn + 1) := by aesop
              simp [t, hhh]
            case neg hhh =>
              simp [B] at hhh
              simp [hhh]
              intro ui
              apply False.elim
              clear A B t
              have hj:↑ind = nn + 1 := by
                clear hhh
                omega
              clear ui hh
              have io: ind = Fin.mk ind.val (by aesop) := by
                simp [Fin.mk]
              rw [io] at hhh
              simp [hj] at hhh
      have st_ := st n (by omega)
      simp [pr] at st_
      rw [st_]
      have r: ↑ind ≤ n := by
        let st := @Fin.isLt (n+1) ind
        apply @Nat.le_of_lt_succ _ n st
      simp [r]

lemma Kronecker2 {T: Type}
                 [AddCommMonoid T]
                 (N: ℕ)
                 (pos: N > 0)
                 (S: Fin N → Fin N → T):
fs (fun i: Fin N =>
       fs (fun j: Fin N => if(i=j) then S j i else 0)
   ) =
fs (fun i: Fin N => S i i) := by
  let st(ind: Fin N) := @Kronecker T _ N pos ind (fun j:Fin N => S j ind)
  simp [st]
