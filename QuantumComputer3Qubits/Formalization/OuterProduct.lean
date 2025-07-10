import QuantumComputer3Qubits.Formalization.InnerProduct
-- This file formalizes outer product: |a⟩⟨b| (in Dirac notation)

-- OP means "Outer Product"
def OP{T: Type}
      [AddCommMonoid T]
      [m: Module ℂ T]
      [IP T]
      (t1 t2: T): T →ₗ[ℂ] T :=
{
  toFun(x: T) := (IP.f t2 x) • t1
  map_add' := by
    simp [IP.distrRight]
    intro x y
    generalize r₁:IP.f t2 x = X
    generalize r₂:IP.f t2 y = Y
    clear x y r₁ r₂
    simp [m.add_smul]
  map_smul' := by
    simp [IP.smulRight]
    intro
    intro
    module
}
