import QuantumComputer3Qubits.Formalization.QubitBasic
import QuantumComputer3Qubits.Formalization.QubitIndexed
-- This file formalizes registry and subregistry states

open scoped TensorProduct

-- State of registry of 1 qubit
@[reducible]
def StateReg1: Type := QubitState

-- State of 2-qubit registry
@[reducible]
def StateReg2: Type := QubitState ⊗[ℂ] QubitState

-- State of 1-qubit subregistry in 3-qubit registry
-- i1 is qubit index
@[reducible]
def StateReg1Ind(i1: Fin 3):Type := QubitInd i1

-- State of 2-qubit subregistry in 3-qubit registry.
-- i1 i2 are qubit indexes.
-- i1 < i2 is necessary to make sure that:
--   1. This is really 2-qubit subregistry and indexes don't
--      point on one and the same qubit
--   2. There no two different types (StateReg2Ind i1 i2 and
--      StateReg2Ind i2 i1) formalizing the same subregistry.
@[reducible]
def StateReg2Ind(i1 i2: Fin 3)(_: (i1 < i2)):Type := (QubitInd i1) ⊗[ℂ] (QubitInd i2)

-- State of 3-qubit registry
@[reducible]
def StateReg3:Type := (StateReg2Ind 0 1 (by simp)) ⊗[ℂ] (QubitInd 2)

structure Decomp2(T: Type)
                 [AddCommMonoid T]
                 [Module ℂ T] where
t1: T
t2: T
prop: ∀t:T, ∃c1 c2: ℂ, (c1•t1) + (c2•t2) = t

structure Decomp4(T: Type)
                 [AddCommMonoid T]
                 [Module ℂ T] where
t1: T
t2: T
t3: T
t4: T
prop: ∀t:T, ∃c1 c2 c3 c4: ℂ,
      c1 • t1 + c2 • t2 + c3 • t3 + c4 • t4 = t

structure Decomp8(T: Type)
                 [AddCommMonoid T]
                 [Module ℂ T] where
t1: T
t2: T
t3: T
t4: T
t5: T
t6: T
t7: T
t8: T
prop: ∀t:T, ∃c1 c2 c3 c4 c5 c6 c7 c8: ℂ,
c1 • t1 + c2 • t2 + c3 • t3 + c4 • t4 +
c5 • t5 + c6 • t6 + c7 • t7 + c8 • t8 = t

def ds2_0: Decomp2 (StateReg1Ind 0) :=
{
  -- Quantum analog of a qubit containing 0
  t1 := fun x:X1 => match x with
                   | X1.a => 1
                   | X1.b => 0

  -- Quantum analog of a qubit containing 1
  t2 := fun x:X1 => match x with
                   | X1.a => 0
                   | X1.b => 1

  prop := by
    intro t
    exists t X1.a
    exists t X1.b
    ext i
    cases i
    all_goals simp [HAdd.hAdd]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

def ds2_1: Decomp2 (StateReg1Ind 1) :=
{
  -- Quantum analog of a qubit containing 0
  t1 := fun x:X2 => match x with
                   | X2.a => 1
                   | X2.b => 0

  -- Quantum analog of a qubit containing 1
  t2 := fun x:X2 => match x with
                   | X2.a => 0
                   | X2.b => 1

  prop := by
    intro t
    exists t X2.a
    exists t X2.b
    ext i
    cases i
    all_goals simp [HAdd.hAdd]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

def ds2_2: Decomp2 (StateReg1Ind 2) :=
{
  -- Quantum analog of a qubit containing 0
  t1 := fun x:X3 => match x with
                   | X3.a => 1
                   | X3.b => 0

  -- Quantum analog of a qubit containing 1
  t2 := fun x:X3 => match x with
                   | X3.a => 0
                   | X3.b => 1

  prop := by
    intro t
    exists t X3.a
    exists t X3.b
    ext i
    cases i
    all_goals simp [HAdd.hAdd]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

open scoped TensorProduct

noncomputable
def ds4(T1 T2: Type)
       [AddCommMonoid T1]
       [Module ℂ T1]
       [AddCommMonoid T2]
       [Module ℂ T2]
       (dc1: Decomp2 T1)
       (dc2: Decomp2 T2):
       Decomp4 (T1 ⊗[ℂ] T2) :=
{
  t1 := (TensorProduct.tmul ℂ dc1.t1 dc2.t1)
  t2 := (TensorProduct.tmul ℂ dc1.t1 dc2.t2)
  t3 := (TensorProduct.tmul ℂ dc1.t2 dc2.t1)
  t4 := (TensorProduct.tmul ℂ dc1.t2 dc2.t2)

  prop := by
    intro t
    apply TensorProduct.induction_on
          (motive := fun x:(T1 ⊗[ℂ] T2) => ∃ c1 c2 c3 c4,
                                            c1 • dc1.t1 ⊗ₜ[ℂ] dc2.t1 + c2 • dc1.t1 ⊗ₜ[ℂ] dc2.t2 + c3 • dc1.t2 ⊗ₜ[ℂ] dc2.t1 + c4 • dc1.t2 ⊗ₜ[ℂ] dc2.t2 = x)
    {
      exists 0
      exists 0
      exists 0
      exists 0
      simp
    }
    {
      intro x y
      let ⟨x1, ⟨x2, st_x⟩⟩ := dc1.prop x
      let ⟨y1, ⟨y2, st_y⟩⟩ := dc2.prop y
      exists x1*y1
      exists x1*y2
      exists x2*y1
      exists x2*y2
      rw [Eq.symm st_x]
      rw [Eq.symm st_y]
      simp [TensorProduct.tmul_add, TensorProduct.add_tmul]
      simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
      module
    }
    {
      intro x y
      intro ih1 ih2
      let ⟨x1, ⟨x2, ⟨x3, ⟨x4, st_x⟩⟩⟩⟩ := ih1
      let ⟨y1, ⟨y2, ⟨y3, ⟨y4, st_y⟩⟩⟩⟩ := ih2
      exists x1+y1
      exists x2+y2
      exists x3+y3
      exists x4+y4
      rw [Eq.symm st_x]
      rw [Eq.symm st_y]
      module
    }
}

noncomputable
def ds8(T1 T2: Type)
       [AddCommMonoid T1]
       [Module ℂ T1]
       [AddCommMonoid T2]
       [Module ℂ T2]
       (dc1: Decomp4 T1)
       (dc2: Decomp2 T2):
       Decomp8 (T1 ⊗[ℂ] T2) :=
{
  t1 := (TensorProduct.tmul ℂ dc1.t1 dc2.t1)
  t2 := (TensorProduct.tmul ℂ dc1.t1 dc2.t2)
  t3 := (TensorProduct.tmul ℂ dc1.t2 dc2.t1)
  t4 := (TensorProduct.tmul ℂ dc1.t2 dc2.t2)
  t5 := (TensorProduct.tmul ℂ dc1.t3 dc2.t1)
  t6 := (TensorProduct.tmul ℂ dc1.t3 dc2.t2)
  t7 := (TensorProduct.tmul ℂ dc1.t4 dc2.t1)
  t8 := (TensorProduct.tmul ℂ dc1.t4 dc2.t2)

  prop := by
    intro t
    apply TensorProduct.induction_on
          (motive := fun x:(T1 ⊗[ℂ] T2) => ∃ c1 c2 c3 c4 c5 c6 c7 c8,
                                            c1 • dc1.t1 ⊗ₜ[ℂ] dc2.t1 + c2 • dc1.t1 ⊗ₜ[ℂ] dc2.t2 + c3 • dc1.t2 ⊗ₜ[ℂ] dc2.t1 + c4 • dc1.t2 ⊗ₜ[ℂ] dc2.t2 + c5 • dc1.t3 ⊗ₜ[ℂ] dc2.t1 + c6 • dc1.t3 ⊗ₜ[ℂ] dc2.t2 + c7 • dc1.t4 ⊗ₜ[ℂ] dc2.t1 + c8 • dc1.t4 ⊗ₜ[ℂ] dc2.t2 = x)
    {
      exists 0
      exists 0
      exists 0
      exists 0
      exists 0
      exists 0
      exists 0
      exists 0
      simp
    }
    {
      intro x y
      let ⟨x1, ⟨x2, ⟨x3, ⟨x4, st_x⟩⟩⟩⟩ := dc1.prop x
      let ⟨y1, ⟨y2, st_y⟩⟩ := dc2.prop y
      exists x1*y1
      exists x1*y2
      exists x2*y1
      exists x2*y2
      exists x3*y1
      exists x3*y2
      exists x4*y1
      exists x4*y2
      rw [Eq.symm st_x]
      rw [Eq.symm st_y]
      simp [TensorProduct.tmul_add, TensorProduct.add_tmul]
      simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
      module
    }
    {
      intro x y
      intro ih1 ih2
      let ⟨x1, ⟨x2, ⟨x3, ⟨x4, ⟨x5, ⟨x6, ⟨x7, ⟨x8, st_x⟩⟩⟩⟩⟩⟩⟩⟩ := ih1
      let ⟨y1, ⟨y2, ⟨y3, ⟨y4, ⟨y5, ⟨y6, ⟨y7, ⟨y8, st_y⟩⟩⟩⟩⟩⟩⟩⟩ := ih2
      exists x1+y1
      exists x2+y2
      exists x3+y3
      exists x4+y4
      exists x5+y5
      exists x6+y6
      exists x7+y7
      exists x8+y8
      rw [Eq.symm st_x]
      rw [Eq.symm st_y]
      module
    }
}

noncomputable
def DS: Decomp8 StateReg3 := ds8 (StateReg2Ind 0 1 (by simp)) (QubitInd 2)
                                 (ds4 (QubitInd 0) (QubitInd 1) ds2_0 ds2_1)
                                 ds2_2
