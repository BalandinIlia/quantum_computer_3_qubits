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
def QubitSet1(i1: Fin 3):Type := QubitInd i1
#synth Module ℂ (QubitSet1 1)

@[reducible]
def QubitSet2(i1 i2: Fin 3)(neq: (i1 < i2)):Type := (QubitInd i1) ⊗[ℂ] (QubitInd i2)

@[reducible]
def QubitSet3:Type := (QubitSet2 0 1 (by simp)) ⊗[ℂ] (QubitInd 2)
