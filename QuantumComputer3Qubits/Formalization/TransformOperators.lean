import QuantumComputer3Qubits.Formalization.Operators
import QuantumComputer3Qubits.Formalization.LinearEquivRegistryState

-- TO means "Transform Operators"
namespace TO

noncomputable
def o1_oi1(i: Fin 3) : OP.o1 ≃ₗ[ℂ] (OP.oi1 i) :=
{
  toFun(o: OP.o1) := by
    let tr1 := LinearEquiv.toLinearMap (LER.reg1i_reg1 i)
    let tr2 := LinearEquiv.toLinearMap (LinearEquiv.symm (LER.reg1i_reg1 i))
    simp [OP.o1] at o
    exact LinearMap.comp tr2 (LinearMap.comp o tr1)
  invFun(o: OP.oi1 i) := by
    let tr1 := LinearEquiv.toLinearMap (LER.reg1i_reg1 i)
    let tr2 := LinearEquiv.toLinearMap (LinearEquiv.symm (LER.reg1i_reg1 i))
    simp [OP.oi1] at o
    exact LinearMap.comp tr1 (LinearMap.comp o tr2)
  map_add' := by
    simp [LER.reg1i_reg1]
    aesop
  map_smul' := by
    simp [LER.reg1i_reg1]
    aesop
  left_inv := by
    simp [Function.LeftInverse]
    intro x
    ext a b
    simp
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro x
    ext a
    simp
}

noncomputable
def o2_oi2(i1 i2: Fin 3)(ord: i1 < i2) : OP.o2 ≃ₗ[ℂ] (OP.oi2 i1 i2 ord) :=
{
  toFun(o: OP.o2) := by
    let tr1 := LinearEquiv.toLinearMap (LER.reg2i_reg2 i1 i2 ord)
    let tr2 := LinearEquiv.toLinearMap (LinearEquiv.symm (LER.reg2i_reg2 i1 i2 ord))
    simp [OP.o2] at o
    exact LinearMap.comp tr2 (LinearMap.comp o tr1)
  invFun(o: OP.oi2 i1 i2 ord) := by
    let tr1 := LinearEquiv.toLinearMap (LER.reg2i_reg2 i1 i2 ord)
    let tr2 := LinearEquiv.toLinearMap (LinearEquiv.symm (LER.reg2i_reg2 i1 i2 ord))
    simp [OP.oi2] at o
    exact LinearMap.comp tr1 (LinearMap.comp o tr2)
  map_add' := by
    simp [LER.reg2i_reg2]
    aesop
  map_smul' := by
    simp [LER.reg2i_reg2]
    aesop
  left_inv := by
    simp [Function.LeftInverse]
    intro x
    ext a b
    simp
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro x
    ext a
    simp
}
