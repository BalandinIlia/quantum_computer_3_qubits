import QuantumComputer3Qubits.Formalization.QubitBasic
import QuantumComputer3Qubits.Formalization.QubitIndexed
import QuantumComputer3Qubits.Formalization.Decompose
import QuantumComputer3Qubits.Tests.StateExamples
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

def dc0: DC.Decompose2 (StateReg1Ind 0) :=
{
  bas := fun i: Fin 2 => match i with
  -- Quantum analog of a qubit containing 0
  | 0 => SE.si0 0
  -- Quantum analog of a qubit containing 1
  | 1 => SE.si1 0

  prop := by
    intro t
    exists fun i: Fin 2 => match i with
                           | 0 => t X1.a
                           | 1 => t X1.b
    ext i
    cases i
    all_goals simp [FS.FS2]
    all_goals simp [StateReg1Ind, HAdd.hAdd, SE.si0, SE.si1]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

def dc1: DC.Decompose2 (StateReg1Ind 1) :=
{
  bas := fun i: Fin 2 => match i with
  -- Quantum analog of a qubit containing 0
  | 0 => SE.si0 1
  -- Quantum analog of a qubit containing 1
  | 1 => SE.si1 1

  prop := by
    intro t
    exists fun i: Fin 2 => match i with
                           | 0 => t X2.a
                           | 1 => t X2.b
    ext i
    cases i
    all_goals simp [FS.FS2]
    all_goals simp [StateReg1Ind, HAdd.hAdd, SE.si0, SE.si1]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

def ds2: DC.Decompose2 (StateReg1Ind 2) :=
{
  bas := fun i: Fin 2 => match i with
  -- Quantum analog of a qubit containing 0
  | 0 => SE.si0 2
  -- Quantum analog of a qubit containing 1
  | 1 => SE.si1 2

  prop := by
    intro t
    exists fun i: Fin 2 => match i with
                           | 0 => t X3.a
                           | 1 => t X3.b
    ext i
    cases i
    all_goals simp [FS.FS2]
    all_goals simp [StateReg1Ind, HAdd.hAdd, SE.si0, SE.si1]
    all_goals simp [Add.add]
    all_goals simp [HSMul.hSMul]
    all_goals simp [SMul.smul]
}

noncomputable
def dsReg3: DC.Decompose8 StateReg3 :=
DC.tp_4_3 (StateReg2Ind 0 1 (by simp))
          (QubitInd 2)
          (DC.tp_2_2 (QubitInd 0)
                     (QubitInd 1)
                     ds0
                     ds1
          )
          ds2
