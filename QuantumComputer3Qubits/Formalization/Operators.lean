import QuantumComputer3Qubits.Formalization.RegistryState

-- OP means "operator"
namespace OP

@[reducible]
def o1: Type := StateReg1 →ₗ[ℂ] StateReg1

@[reducible]
def o2: Type := StateReg2 →ₗ[ℂ] StateReg2

@[reducible]
def o3: Type := StateReg3 →ₗ[ℂ] StateReg3

@[reducible]
def oi1(i1: Fin 3):Type :=
  (StateReg1Ind i1) →ₗ[ℂ] (StateReg1Ind i1)

@[reducible]
def oi2(i1 i2: Fin 3)(ord: (i1 < i2)):Type :=
  (StateReg2Ind i1 i2 ord) →ₗ[ℂ] (StateReg2Ind i1 i2 ord)
