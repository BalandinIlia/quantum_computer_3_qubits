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

lemma Equality3(op1 op2: o3):
(∀ v1 v2 v3: CS.CV, (op1 (CS.qqq v1 v2 v3) = op2 (CS.qqq v1 v2 v3))) →
op1 = op2 := by
  intro h
  have t:∀s: StateReg3, op1 s = op2 s := by
    intro s
    let ⟨cX, st_x⟩ := DC.dsReg3.prop s
    simp [FS.FS8, DC.dsReg3, DC.tp_4_2, DC.tp_2_2, DC.dc0, DC.dc1, DC.dc2] at st_x
    simp [st_x]
    simp [CS.qqq] at h
    simp [h]
  aesop

def Core: Type := CS.CV → CS.CV → CS.CV → StateReg3

noncomputable
def o3ByCore(core: Core): o3 := FS.fs
(fun i: Fin 8 => match i with
| 0 => OP (core 0 0 0) (CS.qqq 0 0 0)
| 1 => OP (core 0 0 1) (CS.qqq 0 0 1)
| 2 => OP (core 0 1 0) (CS.qqq 0 1 0)
| 3 => OP (core 0 1 1) (CS.qqq 0 1 1)
| 4 => OP (core 1 0 0) (CS.qqq 1 0 0)
| 5 => OP (core 1 0 1) (CS.qqq 1 0 1)
| 6 => OP (core 1 1 0) (CS.qqq 1 1 0)
| 7 => OP (core 1 1 1) (CS.qqq 1 1 1)
)

noncomputable
def o3AdjByCore(core: Core): o3 := FS.fs
(fun i: Fin 8 => match i with
| 0 => OP (CS.qqq 0 0 0) (core 0 0 0)
| 1 => OP (CS.qqq 0 0 1) (core 0 0 1)
| 2 => OP (CS.qqq 0 1 0) (core 0 1 0)
| 3 => OP (CS.qqq 0 1 1) (core 0 1 1)
| 4 => OP (CS.qqq 1 0 0) (core 1 0 0)
| 5 => OP (CS.qqq 1 0 1) (core 1 0 1)
| 6 => OP (CS.qqq 1 1 0) (core 1 1 0)
| 7 => OP (CS.qqq 1 1 1) (core 1 1 1)
)

theorem o3CoreAdj: ∀c: Core, HC.adj (o3ByCore c) = o3AdjByCore c := by
  intro c
  let ⟨A,prEx,prEq⟩ := HC.adjEx! (o3ByCore c)
  simp at prEx prEq
  have eq1: HC.adj (o3ByCore c) = A := by
    apply prEq (HC.adj (o3ByCore c))
    apply HC.reallyAdj
  have eq2: o3AdjByCore c = A := by
    apply prEq (o3AdjByCore c)
    simp [o3AdjByCore, o3ByCore, FS.FS8]
    apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjSum
    all_goals try apply HC.adjOP
  clear prEx prEq
  aesop
