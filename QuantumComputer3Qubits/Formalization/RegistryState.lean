import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import QuantumComputer3Qubits.Formalization.QubitBasic
import QuantumComputer3Qubits.Formalization.QubitIndexed

open scoped TensorProduct

@[reducible]
def StateReg1: Type := QubitState

@[reducible]
def StateReg2: Type := QubitState ⊗[ℂ] QubitState

@[reducible]
def StateReg1Ind(i1: Fin 3):Type := QubitInd i1

@[reducible]
def StateReg2Ind(i1 i2: Fin 3)(_: (i1 < i2)):Type := (QubitInd i1) ⊗[ℂ] (QubitInd i2)

@[reducible]
def StateReg3:Type := (StateReg2Ind 0 1 (by simp)) ⊗[ℂ] (QubitInd 2)
