import QuantumComputer3Qubits.Formalization.FiniteSum

namespace Test_FiniteSum
open FS

theorem testSum0{T: Type}
                [AddCommMonoid T]
                (F: Fin 0 → T):fs F = 0 := by
  simp [fs, sumPartial.eq_def]

theorem testSum1{T: Type}
                [AddCommMonoid T]
                (F: Fin 1 → T):
  fs F = F 0 := by
  simp [fs, sumPartial.eq_def]

theorem testSum2{T: Type}
                [AddCommMonoid T]
                (F: Fin 2 → T):
  fs F = F 0 + F 1 := by
  simp [fs, sumPartial.eq_def]

theorem testSum3{T: Type}
                [AddCommMonoid T]
                (F: Fin 3 → T):
  fs F = F 0 + F 1 + F 2 := by
  simp [fs, sumPartial.eq_def]

theorem testSum4{T: Type}
                [AddCommMonoid T]
                (F: Fin 4 → T):
  fs F = F 0 + F 1 + F 2 + F 3 := by
  simp [fs, sumPartial.eq_def]

theorem testSum5{T: Type}
                [AddCommMonoid T]
                (F: Fin 5 → T):
  fs F = F 0 + F 1 + F 2 + F 3 + F 4 := by
  simp [fs, sumPartial.eq_def]

theorem testSum6{T: Type}
                [AddCommMonoid T]
                (F: Fin 6 → T):
  fs F = F 0 + F 1 + F 2 + F 3 + F 4 + F 5 := by
  simp [fs, sumPartial.eq_def]

theorem testBasisDecomp1(T: Type)
                        [AddCommMonoid T]
                        [Module ℂ T]
                        (bas: Basis (Fin 1) ℂ T)
                        (x: T) :
basisRepr 1 (by aesop) T bas x := by
  simp [basisRepr]
  simp [fs]
  simp [sumPartial.eq_def]
  have tmp:
    (∑ i, (bas.repr x) i • bas i = (bas.repr x) 0 • bas 0) →
    (x = (bas.repr x) 0 • bas 0) := by
    rw [bas.sum_repr x]
    intro h
    apply h
  apply tmp
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_zero]
  simp

theorem testBasisDecomp2(T: Type)
                        [AddCommMonoid T]
                        [Module ℂ T]
                        (bas: Basis (Fin 2) ℂ T)
                        (x: T) :
basisRepr 2 (by aesop) T bas x := by
  simp [basisRepr]
  simp [fs]
  simp [sumPartial.eq_def]
  have tmp:
    (∑ i, (bas.repr x) i • bas i = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1) →
    (x = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1) := by
    rw [bas.sum_repr x]
    intro h
    apply h
  apply tmp
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_zero]
  simp

theorem testBasisDecomp3(T: Type)
                        [AddCommMonoid T]
                        [Module ℂ T]
                        (bas: Basis (Fin 3) ℂ T)
                        (x: T) :
basisRepr 3 (by aesop) T bas x := by
  simp [basisRepr]
  simp [fs]
  simp [sumPartial.eq_def]
  have tmp:
    (∑ i, (bas.repr x) i • bas i = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1 + (bas.repr x) 2 • bas 2) →
    (x = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1 + (bas.repr x) 2 • bas 2) := by
    rw [bas.sum_repr x]
    intro h
    apply h
  apply tmp
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_zero]
  simp

theorem testBasisDecomp4(T: Type)
                        [AddCommMonoid T]
                        [Module ℂ T]
                        (bas: Basis (Fin 4) ℂ T)
                        (x: T) :
basisRepr 4 (by aesop) T bas x := by
  simp [basisRepr]
  simp [fs]
  simp [sumPartial.eq_def]
  have tmp:
    (∑ i, (bas.repr x) i • bas i = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1 + (bas.repr x) 2 • bas 2 + (bas.repr x) 3 • bas 3) →
    (x = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1 + (bas.repr x) 2 • bas 2 + (bas.repr x) 3 • bas 3) := by
    rw [bas.sum_repr x]
    intro h
    apply h
  apply tmp
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_zero]
  simp

theorem testBasisDecomp5(T: Type)
                        [AddCommMonoid T]
                        [Module ℂ T]
                        (bas: Basis (Fin 5) ℂ T)
                        (x: T) :
basisRepr 5 (by aesop) T bas x := by
  simp [basisRepr]
  simp [fs]
  simp [sumPartial.eq_def]
  have tmp:
    (∑ i, (bas.repr x) i • bas i = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1 + (bas.repr x) 2 • bas 2 + (bas.repr x) 3 • bas 3 + (bas.repr x) 4 • bas 4) →
    (x = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1 + (bas.repr x) 2 • bas 2 + (bas.repr x) 3 • bas 3 + (bas.repr x) 4 • bas 4) := by
    rw [bas.sum_repr x]
    intro h
    apply h
  apply tmp
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_zero]
  simp

theorem testBasisDecomp6(T: Type)
                        [AddCommMonoid T]
                        [Module ℂ T]
                        (bas: Basis (Fin 6) ℂ T)
                        (x: T) :
basisRepr 6 (by aesop) T bas x := by
  simp [basisRepr]
  simp [fs]
  simp [sumPartial.eq_def]
  have tmp:
    (∑ i, (bas.repr x) i • bas i = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1 + (bas.repr x) 2 • bas 2 + (bas.repr x) 3 • bas 3 + (bas.repr x) 4 • bas 4 + (bas.repr x) 5 • bas 5) →
    (x = (bas.repr x) 0 • bas 0 + (bas.repr x) 1 • bas 1 + (bas.repr x) 2 • bas 2 + (bas.repr x) 3 • bas 3 + (bas.repr x) 4 • bas 4 + (bas.repr x) 5 • bas 5) := by
    rw [bas.sum_repr x]
    intro h
    apply h
  apply tmp
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_zero]
  simp
