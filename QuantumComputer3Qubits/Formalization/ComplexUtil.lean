import Mathlib.Data.Complex.Basic

namespace ComplexUtil

lemma Aux:∀c: ℂ, (starRingEnd ℂ) c = star c := by
  aesop

lemma DefStar:∀r1 r2:ℝ, star (Complex.mk r1 r2) = (Complex.mk r1 (-r2)) := by
  aesop

lemma DefMult:∀r1 r2 r3 r4:ℝ, (Complex.mk r1 r2)*(Complex.mk r3 r4) = (Complex.mk (r1*r3 - r2*r4) (r1*r4+r2*r3)) := by
  aesop

lemma DistrSumStar:∀c₁ c₂: ℂ, star (c₁ + c₂) = (star c₁) + (star c₂) := by
  aesop

lemma DistrInvSumStar:∀c₁ c₂: ℂ, (star c₁) + (star c₂) = star (c₁ + c₂) := by
  aesop

lemma EqStar:∀c₁ c₂: ℂ, c₁ = c₂ → (star c₁) = (star c₂) := by
  aesop

lemma DistrMultStar:∀c₁ c₂: ℂ, star (c₁ * c₂) = (star c₁) * (star c₂) := by
  aesop

lemma DoubleStar:∀c: ℂ, star (star c) = c := by
  aesop
