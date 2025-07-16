import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.Decompose
-- This file defines types of linear operators in different
-- (sub)registry linear spaces.

-- OP means "operator"
namespace OP

-- o means "operator"
@[reducible]
def o1: Type := StateReg1 →ₗ[ℂ] StateReg1

@[reducible]
def o2: Type := StateReg2 →ₗ[ℂ] StateReg2

@[reducible]
def o3: Type := StateReg3 →ₗ[ℂ] StateReg3

-- oi means "operator indexed"
@[reducible]
def oi1(i1: Fin 3):Type :=
  (StateReg1Ind i1) →ₗ[ℂ] (StateReg1Ind i1)

@[reducible]
def oi2(i1 i2: Fin 3)(ord: (i1 < i2)):Type :=
  (StateReg2Ind i1 i2 ord) →ₗ[ℂ] (StateReg2Ind i1 i2 ord)

-- identity operator
noncomputable
def idoi1(i: Fin 3): oi1 i :=
{
  toFun(st: StateReg1Ind i) := st
  map_add' := by aesop
  map_smul' := by aesop
}

-- identity operator
noncomputable
def idoi2(i1 i2: Fin 3)(ord: (i1 < i2)): oi2 i1 i2 ord :=
{
  toFun(st: StateReg2Ind i1 i2 ord) := st
  map_add' := by aesop
  map_smul' := by aesop
}

-- identity operator
noncomputable
def ido3: o3 :=
{
  toFun(st: StateReg3) := st
  map_add' := by aesop
  map_smul' := by aesop
}
