import QuantumComputer3Qubits.Formalization.Operators
import QuantumComputer3Qubits.Formalization.LinearEquivRegistryState
-- This file formalizes transformations between operators
-- acting on different linear spaces types representing the
-- same physical system.
--
-- More formally all transformations follow the pattern:
-- 1. There is Type1 representing state of a physical system:
--    quantum registry or quantum subregistry.
-- 2. There is Type2 representing state of a physical system:
--    quantum registry or quantum subregistry.
-- 3. Type1 and Type2 are formally different in Lean (or the
--    same type with different names, no matter), but
--    represent states of identical physical systems.
-- 4. Then we define a transformation tr between operator
--    Type1 → Type1 and operator Type2 → Type2 with the
--    following requirement:
--    ∀ss1:Type1, ∀ss2: Type2, ∀o1:Type1 →ₗ Type1,
--    (ident ss1 ss2) → (ident (o1 ss1) ((tr o1) ss1))
--    where ident means that states are physically identical
--    Informally this can be said as "operators transform
--    physically identical states in physically identical
--    states"

-- TO means "Transform Operators"
namespace TO

-- Type 1: state of quantum registry of 1 qubit
-- Type 2: state of quantum subregistry (in 3-qubit registry)
-- of 1 qubit
-- Physical system 1: quantum registry of 1 qubit
-- Physical system 2: quantum subregistry (in 3-qubit registry)
-- of 1 qubit
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

-- Type 1: state of quantum registry of 2 qubits
-- Type 2: state of quantum subregistry (in 3-qubit registry)
-- of 2 qubits
-- Physical system 1: quantum registry of 2 qubits
-- Physical system 2: quantum subregistry (in 3-qubit registry)
-- of 2 qubits
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

-- Type 1: state of a composite system of 2 quantum
--      registries of 1 qubit. Formally we take two o1
--      operators as input, but conceptually we transform
--      one operator, - their tensor product.
-- Type 2: state of quantum registry of 2 qubits
-- Physical system 1: composite system of 2 quantum
--      registries of 1 qubit
-- Physical system 2: quantum registry of 2 qubits
--
-- tp means "tensor product"
def tpo1o1: OP.o1 →ₗ[ℂ] OP.o1 →ₗ[ℂ] OP.o2 :=
LinearMap.mk₂ ℂ
(fun op1:OP.o1 => fun op2:OP.o1 => TensorProduct.map op1 op2)
(by
  intro m₁ m₂ n
  simp [TensorProduct.map_add_left]
)
(by
  intro c m n
  simp [TensorProduct.map_smul_left]
)
(by
  intro m₁ m₂ n
  simp [TensorProduct.map_add_right]
)
(by
  intro c m n
  simp [TensorProduct.map_smul_right]
)

-- Type 1: state of a composite system of 2 disjoint quantum
--      subregistries of 1 qubit. Formally we take two oi1
--      operators as input, but conceptually we transform
--      one operator, - their tensor product. Disjointness
--      is guaranteed by the condition i1 < i2.
-- Type 2: state of quantum subregistry of 2 qubits
-- Physical system 1: composite system of 2 disjoint quantum
--      subregistries of 1 qubit
-- Physical system 2: quantum subregistry of 2 qubits
noncomputable
-- tp means "tensor product"
def tpo1o1i(i1 i2: Fin 3)(ord: i1 < i2):
(OP.oi1 i1) →ₗ[ℂ] (OP.oi1 i2) →ₗ[ℂ] (OP.oi2 i1 i2 ord) :=
LinearMap.mk₂ ℂ
(fun op1:(OP.oi1 i1) => fun op2:(OP.oi1 i2) => TensorProduct.map op1 op2)
(by
  intro m₁ m₂ n
  simp [TensorProduct.map_add_left]
)
(by
  intro c m n
  simp [TensorProduct.map_smul_left]
)
(by
  intro m₁ m₂ n
  simp [TensorProduct.map_add_right]
)
(by
  intro c m n
  simp [TensorProduct.map_smul_right]
)

noncomputable
def impl(i1 i2: Fin 3)
        (ord: i1 < i2)
        (i3: Fin 3)
        (neq1: ¬(i3=i1))
        (neq2: ¬(i3=i2))
        (op2: OP.oi2 i1 i2 ord)
        (op1: OP.oi1 i3): OP.o3 := by
  let tr1 := LinearEquiv.toLinearMap (LER.reg2ireg1i_reg3 i1 i2 ord i3 neq1 neq2)
  let tr2 := LinearEquiv.toLinearMap (LER.reg2ireg1i_reg3 i1 i2 ord i3 neq1 neq2).symm
  let op := TensorProduct.map op2 op1
  exact LinearMap.comp tr1 (LinearMap.comp op tr2)

noncomputable
def tpo2o1i(i1 i2: Fin 3)
        (ord: i1 < i2)
        (i3: Fin 3)
        (neq1: ¬(i3=i1))
        (neq2: ¬(i3=i2)):
(OP.oi2 i1 i2 ord) →ₗ[ℂ] (OP.oi1 i3) →ₗ[ℂ] OP.o3 :=
LinearMap.mk₂ ℂ
(impl i1 i2 ord i3 neq1 neq2)
(by
  intro m₁ m₂ n
  simp [impl]
  simp [TensorProduct.map_add_left]
  aesop
)
(by
  intro m₁ m₂ n
  simp [impl]
  simp [TensorProduct.map_smul_left]
  aesop
)
(by
  intro m₁ m₂ n
  simp [impl]
  simp [TensorProduct.map_add_right]
  aesop
)
(by
  intro m₁ m₂ n
  simp [impl]
  simp [TensorProduct.map_smul_right]
  aesop
)
