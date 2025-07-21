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
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.Decompose
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.OperatorUtils

namespace DeutschJozsaOracle

structure F where
v00: Fin 2
v01: Fin 2
v10: Fin 2
v11: Fin 2

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

lemma helper(pr: Prop)[Decidable pr](s1 s2 s3: StateReg3):
  IP.f (if pr then s1 else s2) s3 =
  if pr then (IP.f s1 s3) else (IP.f s2 s3) := by
  aesop

lemma helper_(pr: Prop)[Decidable pr](f1 f2: OP.o3)(s: StateReg3):
  (if pr then f1 else f2) s =
  if pr then (f1 s) else (f2 s) := by
  aesop

lemma helper2(s: StateReg3):
  IP.f 0 s = 0 := by
  simp [IP.f]

lemma helper3(pr1 pr2: Prop)[Decidable pr1][Decidable pr2](c1 c2: ℂ):
  (if pr1 then (if pr2 then c1 else c2) else c2) =
  (if (pr1 ∧ pr2) then c1 else c2) := by
  aesop

lemma unitar(f: F): HC.isUnitary (oracle f) := by
  let eq := OU.EqStatesByIP
  simp [CS.qqq] at eq

  simp [HC.isUnitary]
  simp [oracle]
  simp [OU.o3CoreAdj]
  apply And.intro
  all_goals simp [OU.o3ByCore, OU.o3AdjByCore, oracleCore]
  all_goals simp [FS.FS8]
  all_goals simp [LinearMap.comp_add, LinearMap.add_comp]
  all_goals simp [OPDouble]
  all_goals simp [eq]
  all_goals simp [OP]
  all_goals apply OU.Equality3
  all_goals intro v1 v2 v3
  all_goals simp [eq]
  all_goals apply OU.Equality3S
  all_goals intro a b c
  all_goals simp [IP.distrLeft, IP.distrRight]
  all_goals simp [helper, helper_]
  all_goals simp [eq]
  all_goals simp [helper2]
  all_goals try simp [helper]
  all_goals try simp [eq, helper2]
  all_goals clear eq
  all_goals simp [helper3]
  all_goals fin_cases v1
  all_goals simp
  all_goals fin_cases v2
  all_goals simp
  all_goals fin_cases a
  all_goals simp
  all_goals fin_cases b
  all_goals simp
  all_goals fin_cases c
  all_goals simp
  all_goals generalize r00: f.v00 = v00
  all_goals try clear v00 r00
  all_goals generalize r01: f.v01 = v01
  all_goals try clear v01 r01
  all_goals generalize r10: f.v10 = v10
  all_goals try clear v10 r10
  all_goals generalize r11: f.v11 = v11
  all_goals try clear v11 r11
  all_goals try fin_cases v00
  all_goals try fin_cases v01
  all_goals try fin_cases v10
  all_goals try fin_cases v11
  all_goals simp
  all_goals fin_cases v3
  all_goals simp
