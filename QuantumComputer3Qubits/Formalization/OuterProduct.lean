import QuantumComputer3Qubits.Formalization.InnerProduct

def OP{T: Type}
      [AddCommMonoid T]
      [m: Module ℂ T]
      [IP T]
      (t: T): T →ₗ[ℂ] T :=
{
  toFun(x: T) := (IP.f t x) • t
  map_add' := by
    simp [IP.distrRight]
    intro x y
    generalize r₁:IP.f t x = X
    generalize r₂:IP.f t y = Y
    clear x y r₁ r₂
    simp [m.add_smul]
  map_smul' := by
    simp [IP.smulRight]
    intro
    intro
    module
}
