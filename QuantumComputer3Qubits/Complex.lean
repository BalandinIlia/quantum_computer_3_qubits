import Mathlib.Data.Complex.Basic

lemma ComplexStar:∀r1 r2:ℝ, (starRingEnd ℂ) (Complex.mk r1 r2) = (Complex.mk r1 (-r2)) := by
  aesop

lemma ComplexMult:∀r1 r2 r3 r4:ℝ, (Complex.mk r1 r2)*(Complex.mk r3 r4) = (Complex.mk (r1*r3 - r2*r4) (r1*r4+r2*r3)) := by
  aesop
