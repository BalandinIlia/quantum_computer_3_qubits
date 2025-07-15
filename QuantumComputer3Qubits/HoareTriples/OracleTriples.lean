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
import QuantumComputer3Qubits.Formalization.Language
import QuantumComputer3Qubits.Formalization.FiniteSum
import QuantumComputer3Qubits.Formalization.Decompose
import QuantumComputer3Qubits.Formalization.ClassicalStates
import QuantumComputer3Qubits.Formalization.OperatorUtilsHard
import QuantumComputer3Qubits.Formalization.OperatorUtils
import QuantumComputer3Qubits.HoareTriples.Oracle

namespace HoareOracle
open Hoare

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

noncomputable
def tmp(v1 v2: Fin 2):StateReg2Ind 0 1 (by aesop) :=
        CS.qqi v1 v2 0 1 (by aesop)
noncomputable
def stateBeforeRaw: StateReg3 :=
TensorProduct.tmul ℂ ((tmp 0 0) +
                      (tmp 0 1) +
                      (tmp 1 0) +
                      (tmp 1 1))
                     ((CS.qi 0 2)  + mo • (CS.qi 1 2))

noncomputable
def r:ℂ := 1/(2*sqrt2)
noncomputable
def stateBefore: StateReg3 := (r:ℂ) • stateBeforeRaw

def inv(x: Fin 2): ℂ :=
match x with
| 0 => 1
| 1 => mo

noncomputable
def stateAfterRaw(f: F): StateReg3 :=
TensorProduct.tmul ℂ (((inv f.v00) • (tmp 0 0)) +
                      ((inv f.v01) • (tmp 0 1)) +
                      ((inv f.v10) • (tmp 1 0)) +
                      ((inv f.v11) • (tmp 1 1)))
                     ((CS.qi 0 2) + mo • (CS.qi 1 2))
noncomputable
def r2:ℝ := 1/2
noncomputable
def stateAfter(f: F): StateReg3 := (r:ℂ) • (stateAfterRaw f)

set_option maxHeartbeats 100000000

theorem oracleTriple(f: F):
transforms (State.s3 stateBefore)
           (Prog.gate3 (oracle f) (unitar f))
           (State.s3 (stateAfter f)) := by
let eq := OU.EqStatesByIP
simp [CS.qqq] at eq

simp [transforms]
apply And.intro
{
    simp [stateBefore]
    simp [r, stateBeforeRaw]
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
    simp [stateAfter]
    simp [r, stateAfterRaw]
    simp [tmp]
    simp [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul]
    simp [IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight]
    all_goals generalize f.v00 = v00
    all_goals generalize f.v01 = v01
    all_goals generalize f.v10 = v10
    all_goals generalize f.v11 = v11
    all_goals fin_cases v00
    all_goals fin_cases v01
    all_goals fin_cases v10
    all_goals fin_cases v11
    all_goals simp [inv, eq]
    all_goals simp [mo]
    all_goals ring_nf
    all_goals rw [ComplexUtil.Aux]
    all_goals rw [l3Sqrt2]
    all_goals clear eq
    all_goals rw [l1Sqrt2]
    all_goals simp [l2Sqrt2]
}
{
    let pr := Inf.Ax.UTF3 (OP stateBefore stateBefore) (oracle f) (unitar f)
    have repl: ((oracle f • OP stateBefore stateBefore) • HC.adj (oracle f)) = OP (stateAfter f) (stateAfter f) := by
        clear pr
        simp [oracle]
        simp [OU.o3CoreAdj]
        simp [oracleCore, stateAfter, stateAfterRaw]
        generalize f.v00 = v00
        generalize f.v01 = v01
        generalize f.v10 = v10
        generalize f.v11 = v11
        clear f
        all_goals fin_cases v00
        all_goals fin_cases v01
        all_goals fin_cases v10
        all_goals fin_cases v11
        all_goals simp [inv, tmp]
        all_goals apply OU.Equality3
        all_goals intro v1 v2 v3
        all_goals fin_cases v1
        all_goals fin_cases v2
        all_goals fin_cases v3
        all_goals simp [oracleCore, OU.o3ByCore, FS.FS8, OP, IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight, OU.o3AdjByCore, stateBefore, stateAfter, stateBeforeRaw, stateAfterRaw, tmp, TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
        all_goals simp [eq]
        all_goals apply OU.Equality3S
        all_goals intro v1 v2 v3
        all_goals simp [IP.smulLeft, IP.smulRight, IP.distrLeft, IP.distrRight, TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
        all_goals fin_cases v1
        all_goals fin_cases v2
        all_goals fin_cases v3
        all_goals try simp [eq]
        all_goals try dsimp [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try rw [eq]
        all_goals try clear eq
        all_goals try simp [mo]
    rw [repl] at pr
    apply pr
}

#print axioms oracleTriple
