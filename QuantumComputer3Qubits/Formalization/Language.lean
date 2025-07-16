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
import QuantumComputer3Qubits.Formalization.ClassicalStates

namespace Hoare

-- Condition of Hoare triple.
-- Conditions can have several types each of which is
-- specified below.
inductive Cond where
-- Condition "one": this condition is written as {1}.
-- This condition means identity operator.
| c0: Cond
-- Condition based on 1-qubit operator acting on qubit
-- number i
| c1{i: Fin 3}(op: OP.oi1 i): Cond
-- Condition based on 2-qubit operator acting on qubits
-- i1 and i2
| c2{i1 i2: Fin 3}{ord: i1 < i2}(op: OP.oi2 i1 i2 ord): Cond
-- Condition based on 3-qubit operator acting on all qubits
| c3(op: OP.o3): Cond

-- abstract syntax
inductive Prog where
| skip:
    Prog
-- ass means "assign"
-- this program assigns given state to i-th qubit
| ass1 {i:Fin 3}
       (s: StateReg1Ind i)
       (_: IP.f s s = 1):
    Prog
-- this program assigns given state to i1-th and i2-th
-- qubits
| ass2{i1 i2: Fin 3}
      {ord: i1 < i2}
      (s: StateReg2Ind i1 i2 ord)
      (_: IP.f s s = 1):
    Prog
| ass3(s: StateReg3)
      (_: IP.f s s = 1):
    Prog
-- 1-qubit quantum gate
| gate1{i:Fin 3}
       (U: OP.oi1 i)
       -- "un" means "unitary"
       (un: HC.isUnitary U):
    Prog
-- 2-qubit quantum gate
| gate2{i1 i2: Fin 3}
       {ord: i1 < i2}
       (U: OP.oi2 i1 i2 ord)
       (un: HC.isUnitary U):
    Prog
| gate3(U: OP.o3)
       (un: HC.isUnitary U):
    Prog
| seq(p1 p2: Prog):
    Prog

-- Inf2 A p1 p2 B means that:
-- A (p1, p2) B is correct Hoare triple
-- A (p2, p1) B is correct Hoare triple
-- This is used for rules involvind two subprograms
inductive Inf2: Cond → Prog → Prog → Cond → Prop

-- Ax.UTFP formalization for two disjoint 1-qubit systems
-- We put it under Inf2 because operations (quantum gates)
-- can go in any order in it: different orders can be
-- obtained by just changing indexes places
| Ax.UTFP2_1_1(i j: Fin 3)
              (ord: i < j)
              (A: OP.oi2 i j ord)
              (U_i: OP.oi1 i)
              (U_j: OP.oi1 j)
              (un_i: HC.isUnitary U_i)
              (un_j: HC.isUnitary U_j):
      Inf2 (Cond.c2 A)
           (Prog.gate1 U_i un_i)
           (Prog.gate1 U_j un_j)
           (Cond.c2 (
                    (TO.tpo1o1i i j ord U_i U_j) •
                    A •
                    (HC.adj (TO.tpo1o1i i j ord U_i U_j))
           ))

| Ax.UTFP2_2_1(i1 i2 j: Fin 3)
              (ord: i1 < i2)
              (neq1: ¬(j=i1))
              (neq2: ¬(j=i2))
              (A: OP.o3)
              (U_i: OP.oi2 i1 i2 ord)
              (U_j: OP.oi1 j)
              (un_i: HC.isUnitary U_i)
              (un_j: HC.isUnitary U_j):
      Inf2 (Cond.c3 A)
           (Prog.gate2 U_i un_i)
           (Prog.gate1 U_j un_j)
           (Cond.c3 (
                    (TO.tpo2o1i i1 i2 ord j neq1 neq2 U_i U_j) •
                    A •
                    (HC.adj (TO.tpo2o1i i1 i2 ord j neq1 neq2 U_i U_j))
           ))

| Ax.InFP2_1_1(i: Fin 3)
              (j: Fin 3)
              (ord: i < j)
              (t_i: StateReg1Ind i)
              (t_j: StateReg1Ind j)
              (norm_i: (IP.f t_i t_i) = 1)
              (norm_j: (IP.f t_j t_j) = 1):
      Inf2 (Cond.c0)
           (Prog.ass1 t_i norm_i)
           (Prog.ass1 t_j norm_j)
           (Cond.c2
               (TO.tpo1o1i i j ord (OP t_i t_i) (OP t_j t_j))
           )

| Ax.InFP2_2_1(i1 i2: Fin 3)
              (ord: i1 < i2)
              (j: Fin 3)
              (neq1: ¬(j=i1))
              (neq2: ¬(j=i2))
              (t_i: StateReg2Ind i1 i2 ord)
              (t_j: StateReg1Ind j)
              (norm_i: (IP.f t_i t_i) = 1)
              (norm_j: (IP.f t_j t_j) = 1):
      Inf2 (Cond.c0)
           (Prog.ass2 t_i norm_i)
           (Prog.ass1 t_j norm_j)
           (Cond.c3
               (TO.tpo2o1i i1 i2 ord j neq1 neq2 (OP t_i t_i) (OP t_j t_j))
           )

-- Inf3 A p1 p2 p3 B means that:
-- A (p1, p2, p3) B is correct Hoare triple
-- A (p1, p3, p2) B is correct Hoare triple
-- A (p2, p1, p3) B is correct Hoare triple
-- A (p2, p3, p1) B is correct Hoare triple
-- A (p3, p2, p1) B is correct Hoare triple
-- A (p3, p1, p2) B is correct Hoare triple
-- In other word subprograms can go in any order
-- This is used for rules involving three subprograms
inductive Inf3: Cond → Prog → Prog → Prog → Cond → Prop
| Ax.UTFP3(A: OP.o3)
          (U_1: OP.oi1 0)
          (U_2: OP.oi1 1)
          (U_3: OP.oi1 2)
          (un_1: HC.isUnitary U_1)
          (un_2: HC.isUnitary U_2)
          (un_3: HC.isUnitary U_3):
      Inf3 (Cond.c3 A)
           (Prog.gate1 U_1 un_1)
           (Prog.gate1 U_2 un_2)
           (Prog.gate1 U_3 un_3)
           (Cond.c3 (
                    (TO.tp3 U_1 U_2 U_3) •
                    A •
                    (HC.adj (TO.tp3 U_1 U_2 U_3))
           ))

| Ax.InFP3 (t_0: StateReg1Ind 0)
           (t_1: StateReg1Ind 1)
           (t_2: StateReg1Ind 2)
           (norm_0: (IP.f t_0 t_0) = 1)
           (norm_1: (IP.f t_1 t_1) = 1)
           (norm_2: (IP.f t_2 t_2) = 1):
      Inf3 (Cond.c0)
           (Prog.ass1 t_0 norm_0)
           (Prog.ass1 t_1 norm_1)
           (Prog.ass1 t_2 norm_2)
           (Cond.c3
               (TO.tp3 (OP t_0 t_0) (OP t_1 t_1) (OP t_2 t_2))
           )


-- set of inference rules
inductive Inf: Cond → Prog → Cond → Prop

| inf2(A B: Cond)(C1 C2: Prog):
    ((Inf2 A C1 C2 B) ∨
    (Inf2 A C2 C1 B)) →
    Inf A (Prog.seq C1 C2) B

| inf3(A B: Cond)(C1 C2 C3: Prog):
    ((Inf3 A C1 C2 C3 B) ∨
     (Inf3 A C1 C3 C2 B) ∨
     (Inf3 A C2 C1 C3 B) ∨
     (Inf3 A C2 C3 C1 B) ∨
     (Inf3 A C3 C1 C2 B) ∨
     (Inf3 A C3 C2 C1 B)) →
    Inf A (Prog.seq (Prog.seq C1 C2) C3) B

-- rule for skip program
| Ax.Sk(A: Cond): Inf A Prog.skip A

-- version of Ax.UTF rule from the main article for 1-qubit
-- quantum gate
| Ax.UTF1{i: Fin 3} -- index of qubit
         (A U: (OP.oi1 i)) -- condition and gate operator
         (un: HC.isUnitary U): -- gate operator must be unitary
      Inf (Cond.c1 A)
          (Prog.gate1 U un)
          (Cond.c1 ((U • A) • (HC.adj U)))

-- version of Ax.UTF rule from the main article for 2-qubit
-- quantum gate
| Ax.UTF2{i1 i2: Fin 3}
         {ord: i1 < i2}
         (A U: (OP.oi2 i1 i2 ord))
         (un: HC.isUnitary U):
      Inf (Cond.c2 A)
          (Prog.gate2 U un)
          (Cond.c2 ((U • A)•(HC.adj U)))

-- version of Ax.UTF rule from the main article for 3-qubit
-- quantum gate
| Ax.UTF3(A U: OP.o3)
         (un: HC.isUnitary U):
      Inf (Cond.c3 A)
          (Prog.gate3 U un)
          (Cond.c3 ((U • A)•(HC.adj U)))

-- Now we start with Ax.Inf rule. This rule depends on two
-- sets of qubits: S, - system staying untouched and x, -
-- system being assigned. Each Ax.Inf version in the code
-- has two numbers going after its name: size of S and
-- size of x
| Ax.Inf_1_1(iS iX: Fin 3)-- "addresses" of S and x systems
            (neq: ¬(iS = iX))-- system disjointness proposition
            (A_S: OP.oi1 iS)
            (t: StateReg1Ind iX)
            (norm: (IP.f t t) = 1):
      Inf (Cond.c1 A_S)
          (Prog.ass1 t norm)
          (by
             let pr := (iS < iX)
             by_cases pr
             exact Cond.c2 (TO.tpo1o1i iS iX (by aesop) A_S (OP t t))
             exact Cond.c2 (TO.tpo1o1i iX iS (by omega) (OP t t) A_S)
          )

| Ax.Inf_2_1(iS1 iS2 iX: Fin 3)-- "addresses" of S and x systems
            -- This proposition (iS1 < iS2) does not limit
            -- scope of rule applicability. It just defines
            -- order in which iS1 and iS2 should be passed to
            -- the rule
            (ord: iS1 < iS2)
            (neq1: ¬(iX = iS1))-- system disjointness proposition
            (neq2: ¬(iX = iS2))-- system disjointness proposition
            (A_S: OP.oi2 iS1 iS2 ord)
            (t: StateReg1Ind iX)
            (norm: (IP.f t t) = 1):
      Inf (Cond.c2 A_S)
          (Prog.ass1 t norm)
          (Cond.c3 (TO.tpo2o1i iS1 iS2 ord iX neq1 neq2 A_S (OP t t)))

| Ax.Inf_1_2(iS iX1 iX2: Fin 3)
            (ord: iX1 < iX2)
            (neq1: ¬(iS = iX1))
            (neq2: ¬(iS = iX2))
            (A_S: OP.oi1 iS)
            (t: StateReg2Ind iX1 iX2 ord)
            (norm: (IP.f t t) = 1):
      Inf (Cond.c1 A_S)
          (Prog.ass2 t norm)
          (Cond.c3 (TO.tpo2o1i iX1 iX2 ord iS neq1 neq2 (OP t t) A_S))

| R.SC: ∀A B C: Cond, ∀S1 S2: Prog, Inf A S1 B → Inf B S2 C → Inf A (Prog.seq S1 S2) C

| R.CC.P_1_1 (iA iB: Fin 3)
             (N: ℕ)
             (pos: N > 0)
             (A: Fin N → (OP.oi1 iA))
             (B: Fin N → (OP.oi1 iB))
             (lam: Fin N → ℝ)
             (_: ∀i: Fin N, lam i ≥ 0)
             (_: FS.fs lam ≤ 1)
             (C: Prog)
             (_: ∀i: Fin N, Inf (Cond.c1 (A i)) C (Cond.c1 (B i))):
      Inf (Cond.c1 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (A i))))
          C
          (Cond.c1 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (B i))))

| R.CC.P_1_3 (iA: Fin 3)
             (N: ℕ)
             (pos: N > 0)
             (A: Fin N → (OP.oi1 iA))
             (B: Fin N → (OP.o3))
             (lam: Fin N → ℝ)
             (_: ∀i: Fin N, lam i ≥ 0)
             (_: FS.fs lam ≤ 1)
             (C: Prog)
             (_: ∀i: Fin N, Inf (Cond.c1 (A i)) C (Cond.c3 (B i))):
      Inf (Cond.c1 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (A i))))
          C
          (Cond.c3 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (B i))))

-- This is R.El rule: {A_SA}C{B}, SA ∩ S = 0 → {A_SA ⊗ I_S}C{B}
-- Here we write this rule for the case when both SA and S
-- are one bit
| R.El_1_1 (iSA iS: Fin 3) -- SA and S indexes
           (A: OP.oi1 iSA)
           (neq: ¬(iSA = iS)) -- SA ∩ S
           (C: Prog)
           (B: Cond)
           (tr: Inf (Cond.c1 A) C B): -- {A_SA}C{B}
      -- {A_SA ⊗ I_S}C{B}
      Inf (by -- Here we construct {A_SA ⊗ I_S}
             let pr: Prop := iSA < iS
             by_cases pr
             exact Cond.c2 (TO.tpo1o1i iSA iS (by omega) A (OP.idoi1 iS))
             exact Cond.c2 (TO.tpo1o1i iS iSA (by omega) (OP.idoi1 iS) A)
          )
          C
          B

| R.El_2_1 (iSA1 iSA2 iS: Fin 3) -- SA and S indexes
           (ord: iSA1 < iSA2)
           (A: OP.oi2 iSA1 iSA2 ord)
           (neq1: ¬(iS = iSA1))(neq2: ¬(iS = iSA2)) -- SA ∩ S
           (C: Prog)
           (B: Cond)
           (tr: Inf (Cond.c2 A) C B): -- {A_SA}C{B}
      -- {A_SA ⊗ I_S}C{B}
      Inf (Cond.c3 (TO.tpo2o1i iSA1 iSA2 ord iS neq1 neq2 A (OP.idoi1 iS))) -- {A_SA ⊗ I_S}
          C
          B

| R.El_1_2 (iSA iS1 iS2: Fin 3) -- SA and S indexes
           (A: OP.oi1 iSA)
           (ord: iS1 < iS2)
           (neq1: ¬(iSA = iS1))(neq2: ¬(iSA = iS2)) -- SA ∩ S
           (C: Prog)
           (B: Cond)
           (tr: Inf (Cond.c1 A) C B): -- {A_SA}C{B}
      -- {A_SA ⊗ I_S}C{B}
      Inf (Cond.c3 (TO.tpo2o1i iS1 iS2 ord iSA neq1 neq2 (OP.idoi2 iS1 iS2 ord) A)) -- {A_SA ⊗ I_S}
          C
          B

inductive State where
| s1{i:Fin 3}(s: StateReg1Ind i):
      State
| s2{i1 i2: Fin 3}{ord: i1 < i2}(s: StateReg2Ind i1 i2 ord):
      State
| s3(s: StateReg3):
      State

noncomputable
def CondSt(s: State): Cond := match s with
| State.s1 s => Cond.c1 (OP s s)
| State.s2 s => Cond.c2 (OP s s)
| State.s3 s => Cond.c3 (OP s s)

def transforms(sBeg: State)(prog: Prog)(sFin: State): Prop :=
(
    match sBeg with
    | State.s1 s => (IP.f s s) = 1
    | State.s2 s => (IP.f s s) = 1
    | State.s3 s => (IP.f s s) = 1
)
∧
(
    match sFin with
    | State.s1 s => (IP.f s s) = 1
    | State.s2 s => (IP.f s s) = 1
    | State.s3 s => (IP.f s s) = 1
)
∧
Inf (CondSt sBeg) prog (CondSt sFin)
