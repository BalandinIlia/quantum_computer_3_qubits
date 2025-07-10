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
