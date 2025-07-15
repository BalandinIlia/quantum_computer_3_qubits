import QuantumComputer3Qubits.Formalization.QubitBasic
import QuantumComputer3Qubits.Formalization.QubitIndexed
import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Formalization.Operators
import QuantumComputer3Qubits.Formalization.TransformOperators
import QuantumComputer3Qubits.Formalization.ComplexUtil
import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.LinearEquivRegistryState
import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.Language
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.Decompose
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.OperatorUtilsHard
import QuantumComputer3Qubits.Formalization.OperatorUtils

namespace HoareOracle
open Hoare

structure F where
v00: Fin 2
v01: Fin 2
v10: Fin 2
v11: Fin 2

def constant(f: F): Prop := f.v00=0 ∧ f.v01=0 ∧ f.v10=0 ∧ f.v11=0

def balanced(f: F): Prop := ((f.v00:ℕ) +
                             (f.v01:ℕ) +
                             (f.v10:ℕ) +
                             (f.v11:ℕ)) = 2

noncomputable
def oracleCore(f: F): OU.Core := by
  simp [OU.Core]
  intro inp1 inp2 res
  exact CS.qqq inp1
               inp2
               (
                 match inp1, inp2, res with
                 | 0, 0, 0 => if (f.v00 = 0) then 0 else 1
                 | 0, 0, 1 => if (f.v00 = 0) then 1 else 0
                 | 0, 1, 0 => if (f.v01 = 0) then 0 else 1
                 | 0, 1, 1 => if (f.v01 = 0) then 1 else 0
                 | 1, 0, 0 => if (f.v10 = 0) then 0 else 1
                 | 1, 0, 1 => if (f.v10 = 0) then 1 else 0
                 | 1, 1, 0 => if (f.v11 = 0) then 0 else 1
                 | 1, 1, 1 => if (f.v11 = 0) then 1 else 0
               )

noncomputable
def oracle(f: F): OP.o3 := OU.o3ByCore (oracleCore f)

set_option maxHeartbeats 10000000

lemma unitar(f: F): HC.isUnitary (oracle f) := by
  let eq := OU.EqStatesByIP
  simp [CS.qqq] at eq

  simp [HC.isUnitary]
  simp [oracle]
  simp [OU.o3CoreAdj]
  apply And.intro
  all_goals simp [OU.o3ByCore, OU.o3AdjByCore, oracleCore]
  all_goals apply OU.Equality3
  all_goals intro v1 v2 v3
  all_goals simp
  all_goals generalize f.v00 = v00
  all_goals generalize f.v01 = v01
  all_goals generalize f.v10 = v10
  all_goals generalize f.v11 = v11
  all_goals fin_cases v00
  all_goals fin_cases v01
  all_goals fin_cases v10
  all_goals fin_cases v11
  all_goals simp
  all_goals simp [FS.FS8, OP]
  all_goals simp [eq]
  all_goals fin_cases v1
  all_goals fin_cases v2
  all_goals fin_cases v3
  all_goals simp
  all_goals simp [eq]
