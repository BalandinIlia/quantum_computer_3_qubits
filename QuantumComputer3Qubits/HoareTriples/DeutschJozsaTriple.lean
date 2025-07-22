import Mathlib.Data.Real.Sqrt
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
import QuantumComputer3Qubits.Formalization.QWhile
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.Decompose
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.OperatorUtils
import QuantumComputer3Qubits.HoareTriples.DeutschJozsaOracle

namespace DeutschJozsaTriple
open QWhile
open DeutschJozsaOracle

def mo:ℂ := -1

noncomputable
def sqrt2:ℂ := Complex.mk (Real.sqrt 2) 0

private lemma l1Sqrt2: sqrt2⁻¹ * sqrt2⁻¹ = 1/(sqrt2 * sqrt2) := by
  aesop

private lemma l2Sqrt2: sqrt2 * sqrt2 = 2 := by
  simp [sqrt2]
  rw [ComplexUtil.DefMult]
  aesop

private lemma l3Sqrt2: star sqrt2 = sqrt2 := by
  rw [sqrt2]
  rw [ComplexUtil.DefStar]
  aesop

private lemma lemSqrt2:
sqrt2⁻¹ * 2⁻¹ = ((starRingEnd ℂ) sqrt2)⁻¹ * ((starRingEnd ℂ) 2)⁻¹ ∨ sqrt2 = 0 := by
  apply Or.intro_left
  repeat rw [sqrt2]
  repeat rw [ComplexUtil.Aux]
  repeat rw [ComplexUtil.DefStar]
  simp
  apply Or.intro_left
  aesop

def inv(x: Fin 2): ℂ :=
match x with
| 0 => 1
| 1 => mo

noncomputable
def tmp(v1 v2: Fin 2):StateReg2Ind 0 1 (by aesop) :=
    CS.qqi v1 v2 0 1 (by aesop)
noncomputable
def stateBeforeUnnormed: StateReg3 :=
TensorProduct.tmul ℂ ((tmp 0 0) +
                      (tmp 0 1) +
                      (tmp 1 0) +
                      (tmp 1 1))
                     ((CS.qi 0 2)  + mo • (CS.qi 1 2))
noncomputable
def stateBefore: StateReg3 := (1/(2*sqrt2)) • stateBeforeUnnormed

noncomputable
def stateAfterUnnorm(f: F): StateReg3 :=
TensorProduct.tmul ℂ (((inv f.v00) • (tmp 0 0)) +
                      ((inv f.v01) • (tmp 0 1)) +
                      ((inv f.v10) • (tmp 1 0)) +
                      ((inv f.v11) • (tmp 1 1)))
                     ((CS.qi 0 2) + mo • (CS.qi 1 2))
noncomputable
def stateAfter(f: F): StateReg3 := (1/(2*sqrt2)) • (stateAfterUnnorm f)

set_option maxHeartbeats 2000000

theorem oracleTriple(f: F):
classicalHoare (CondRegistry.c3 stateBefore)
               (Prog.gate3 (oracle f) (unitar f))
               (CondRegistry.c3 (stateAfter f)) := by
let eq := OU.EqStatesByIP
simp [CS.qqq] at eq

simp [classicalHoare, CondSt]
apply And.intro
{
  simp [stateBefore]
  simp [stateBeforeUnnormed]
  simp [tmp]
  simp [TensorProduct.add_tmul, TensorProduct.tmul_add]
  simp [IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight]
  simp [eq]
  simp [mo]
  ring_nf
  rw [ComplexUtil.Aux]
  rw [l3Sqrt2]
  rw [l1Sqrt2]
  simp [l2Sqrt2]
}
apply And.intro
{
  simp [stateAfter, stateAfterUnnorm]
  simp [tmp]
  simp [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul]
  simp [IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight]
  simp [inv]
  simp [eq]
  clear eq
  all_goals generalize f.v00 = v00
  all_goals generalize f.v01 = v01
  all_goals generalize f.v10 = v10
  all_goals generalize f.v11 = v11
  all_goals clear f
  all_goals fin_cases v00
  all_goals fin_cases v01
  all_goals fin_cases v10
  all_goals fin_cases v11
  all_goals simp [mo]
  all_goals ring_nf
  all_goals rw [ComplexUtil.Aux]
  all_goals simp [l1Sqrt2, l2Sqrt2, l3Sqrt2]
}
{
  let pr := InfRules.Ax.UTF3 (oracle f) (unitar f) (OP stateBefore stateBefore)
  have repl: (oracle f ∘ₗ (OP stateBefore stateBefore) ∘ₗ (HC.adj (oracle f))) = OP (stateAfter f) (stateAfter f) := by
    clear pr
    simp [oracle]
    simp [OU.o3CoreAdj]
    simp [OU.o3ByCore, OU.o3AdjByCore]
    simp [FS.FS8]
    simp [LinearMap.add_comp, LinearMap.comp_add]
    simp [OPDouble]
    simp [LinearMap.comp_smul]
    simp [OPDouble]
    simp [stateBefore, stateBeforeUnnormed, tmp]
    simp [IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight, TensorProduct.add_tmul, TensorProduct.tmul_add]
    simp [eq]
    ring_nf
    have l1:(starRingEnd ℂ) sqrt2 = sqrt2 := by
      simp [sqrt2]
      rw [ComplexUtil.Aux]
      rw [ComplexUtil.DefStar]
      aesop
    simp [l1]
    have l2:(starRingEnd ℂ) mo = mo := by simp [mo]
    simp [l2]
    apply OU.Equality3
    intro v1 v2 v3
    simp [LinearMap.add_apply]
    simp [OP]
    simp [oracleCore]
    simp [eq]
    simp [stateAfter, stateAfterUnnorm, tmp, inv]
    simp [IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight, TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    simp [eq]
    simp [l1, l2]
    all_goals apply OU.Equality3S
    all_goals intro a1 a2 a3
    simp [IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight, TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    simp [helper]
    simp [IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight, TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    simp [eq]
    simp [helper2]
    clear eq
    simp [l1, l2, mo]
    fin_cases v1
    all_goals simp
    all_goals fin_cases v2
    all_goals simp
    all_goals fin_cases v3
    all_goals simp
    all_goals fin_cases a1
    all_goals simp
    all_goals fin_cases a2
    all_goals simp
    all_goals fin_cases a3
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
    all_goals try apply lemSqrt2
  rw [repl] at pr
  apply pr
}

#print axioms oracleTriple
