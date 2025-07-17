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
-- This file specifies Hoare rules.
--
-- In order to translate rules from the main article into
-- Lean code, we developed an intermediate language
-- for specifying Hoare rules:
-- Each statement in the language is separated into input
-- and output.
-- 1. Input consists of terms of the following types:
--   1.1. System: a set of qubits; if we have two Systems:
--        s1, s2: System, then s1∪s2 is a system which
--        contains all qubits that belong to at least one of
--        the systems.
--   1.2. QuantState s: type parametrized by System. The type
--        represents state of the quantum system.
--   1.3. LinOp s: type parametrized by System. The type
--        represents arbitrary linear operator, acting
--        in the state space of quantum system s.
--        U^ means Hermitian conjugation.
--   1.4. UnitaryOp s: type parametrized by System. The type
--        represents unitary linear operator, acting
--        in the state space of quantum system s.
--   1.5. Prop: proposition, - represents arbitrary
--        proposition written in natural language. Special
--        type of proposition is {A}C{B} - Hoare triple.
--        For proposition we also specify its value through
--        :=. For example: pr: Prop := {A}C{B} means
--        proposition pr stating that {A}C{B} is a correct
--        Hoare triple.
--   1.6. Prog: a program
--        Particular instance of Prog can be spceified with
--        the following abstract syntax:
--        Prog := skip | ass QuantState | gate UnitaryOp |
--                seq Prog Prog | seq Prog Prog Prog
--   1.7. ℕ: natural number
--   1.8. ℝ: real number
--   1.9. Array N Type: array of terms of type Type with
--        lenght N
--   I s is a function of type LinOp s. It generates identity
--   operator
-- 2. Output is just a Hoare triple.
--
-- This language is something in the middle between Lean and
-- inference rules written in natural language:
-- 1. On the one hand it is different from natural language,
--    because it divides all input it typified term, which
--    look like Lean terms.
-- 2. On the other hand it is different from Lean, because:
--   2.1. It does not care about how quantum systems are
--        formalized in Lean (for example just writes s
--        instead i1 i2:Fin 3 ord: i1 < i2)
--   2.2. The same for quantum states, linear operators
--   2.3. Allows to write propositions in a most convenient
--        way, not necessary Lean-readable.
-- So we use this language as an intermediate step between
-- inference rules written in natural language and inference
-- rules written in Lean. In other words each inference rule
-- is first translated from natural language to the
-- intermediate language and then from the intermediate
-- language into Lean.
--
-- Here we present Hoare inference rules rewritten in the
-- intermediate language:
-- Ax.Sk:
--   Input:
--     s: System
--     A: LinOp s
--   Output:
--     {A}Skip{A}
-- Ax.UTF:
--   Input:
--     x: System
--     U: UnitaryOp x
--     A: LinOp x
--   Output:
--     {A} Prog.gate U {U • A • U^}
-- Ax.InF:
--   Input:
--     S: System
--     x: System
--     disj: Prop := S ∩ x = ∅
--     A: LinOp S
--     t: QuantState x
--   Ouput:
--     {A} Prog.ass t {A ⊗ |t⟩⟨t|}
-- R.SC: We don't transfer this rule into
-- Ax.UTFP we separate into two rules: for two system and
-- for 3 systems (4 systems is impossible since we have only
-- 3 qubits):
-- Ax.UTFP2:
--   Input:
--     x_1: System
--     x_2: System
--     disj: Prop := x_1 ∩ x_2 = ∅
--     U_1: UnitaryOp x_1
--     U_2: UnitaryOp x_2
--     A: LinOp (x_1 + x_2)
--   Output:
--     {A} Prog.seq (Prog.gate U_1) (Prog.gate U_2)
--         {(U_1⊗U_2)•A•(U_1⊗U_2)^}
-- Ax.UTFP3:
--   Input:
--     x_1: System
--     x_2: System
--     x_3: System
--     disj: Prop := (x_1 ∩ x_2 = ∅) ∧ (x_1 ∩ x_3 = ∅) ∧
--                   (x_2 ∩ x_3 = ∅)
--     U_1: UnitaryOp x_1
--     U_2: UnitaryOp x_2
--     U_3: UnitaryOp x_3
--     A: LinOp (x_1 + x_2 + x_3)
--   Output:
--     {A} Prog.seq (Prog.gate U_1) (Prog.gate U_2) (Prog.gate U_3)
--         {(U_1⊗U_2⊗U_3)•A•(U_1⊗U_2⊗U_3)^}
-- Ax.InFP is also separated in 2-system case and 3-system
-- case:
-- Ax.InFP2:
--   Input:
--     x_1: System
--     x_2: System
--     disj: Prop := x_1 ∩ x_2 = ∅
--     t_1: QuantState x_1
--     t_2: QuantState x_2
--   Output:
--     {1} Prog.seq (Prog.ass t_1) (Prog.ass t_2)
--         {|t_1⟩⟨t_1| ⊗ |t_2⟩⟨t_2|}
-- Ax.InFP3:
--   Input:
--     x_1: System
--     x_2: System
--     x_3: System
--     disj: Prop := (x_1 ∩ x_2 = ∅) ∧ (x_1 ∩ x_3 = ∅) ∧
--                   (x_2 ∩ x_3 = ∅)
--     t_1: QuantState x_1
--     t_2: QuantState x_2
--     t_3: QuantState x_3
--   Output:
--     {1} Prog.seq (Prog.ass t_1) (Prog.ass t_2) (Prog.ass t_3)
--         {|t_1⟩⟨t_1| ⊗ |t_2⟩⟨t_2| ⊗ |t_3⟩⟨t_3|}
-- R.CC.P:
--   Input:
--     N: ℕ
--     x_A: System
--     x_B: System
--     A: Array N (LinOp x_A)
--     B: Array N (LinOp x_B)
--     λ: Array N ℝ
--     C: Prog
--     pr_λ_pos: ∀i: λ[i]≥0 where [] means addressing
--               particular array element
--     pr_λ_sum: ∑λ[i] ≤ 1
--     hoar: ∀i: {A[i]}C{B[i]}
--   Ouput:
--     {sum (λ[i] * A[i])} C {sum (λ[i] * B[i])}
-- R.El:
--   Input:
--     S_A: System
--     S: System
--     S_B: System
--     disj: S_A ∩ S = ∅
--     A_S_A: LinOp S_A
--     C: Prog
--     B: LinOp B
--     hoar: {A_S_A}C{B}
--   Output:
--     {A_S_A ⊗ (I S)} C {B}

namespace Hoare

def min(i j: Fin 3): Fin 3 := if i < j then i else j
def max(i j: Fin 3): Fin 3 := if i < j then j else i

lemma fin3{A: Prop}(i: Fin 3):
((i=0)→A) →
((i=1)→A) →
((i=2)→A) →
A := by
    intro h1 h2 h3
    fin_cases i
    all_goals aesop

macro "f2" a:ident b:ident : tactic =>
`(tactic|(
    all_goals apply fin3 $a
    all_goals apply fin3 $b
    all_goals try simp [min, max]
    all_goals try omega
    all_goals try aesop
))

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

-- set of inference rules
inductive Inf: Cond → Prog → Cond → Prop

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

-- Ax.Inf rule says:
-- ∀S, x:
--   S∩x=∅ → (∀|t⟩, A_S: {A_S}x:=|t⟩{A_S⊗|t⟩⟨t|})
-- Here: x and S are qubit sets, |t⟩ is state in space of x,
-- A_S is operator in space of S
-- _1_1 means that both systems (S and X) are 1-qubit
| Ax.Inf_1_1
    -- this argument defines S system
    (iS: Fin 3)
    -- this argument defines x system
    (iX: Fin 3)
    -- system disjointness proposition
    (neq: ¬(iS = iX))
    (t: StateReg1Ind iX)(norm: (IP.f t t) = 1)
    (A_S: OP.oi1 iS):
      Inf (Cond.c1 A_S)
          (Prog.ass1 t norm)
          (by
             let pr := (iS < iX)
             by_cases pr
             exact Cond.c2 (TO.tpo1o1i iS iX (by aesop) A_S (OP t t))
             exact Cond.c2 (TO.tpo1o1i iX iS (by omega) (OP t t) A_S)
          )

| Ax.Inf_2_1
    -- S definition
    (iS1 iS2: Fin 3)(ord: iS1 < iS2)
    -- x definition
    (iX: Fin 3)
    -- system disjointness propositions
    (neq1: ¬(iX = iS1))(neq2: ¬(iX = iS2))
    (t: StateReg1Ind iX)(norm: (IP.f t t) = 1)
    (A_S: OP.oi2 iS1 iS2 ord):
      Inf (Cond.c2 A_S)
          (Prog.ass1 t norm)
          (Cond.c3 (TO.tpo2o1i iS1 iS2 ord iX neq1 neq2 A_S (OP t t)))

| Ax.Inf_1_2
    -- S definition
    (iS: Fin 3)
    -- x definition
    (iX1 iX2: Fin 3)(ord: iX1 < iX2)
    -- system disjointness propositions
    (neq1: ¬(iS = iX1))(neq2: ¬(iS = iX2))
    (t: StateReg2Ind iX1 iX2 ord)(norm: (IP.f t t) = 1)
    (A_S: OP.oi1 iS):
      Inf (Cond.c1 A_S)
          (Prog.ass2 t norm)
          (Cond.c3 (TO.tpo2o1i iX1 iX2 ord iS neq1 neq2 (OP t t) A_S))

| R.SC: ∀A B C: Cond, ∀S1 S2: Prog, Inf A S1 B → Inf B S2 C → Inf A (Prog.seq S1 S2) C

-- AX.UTFP rule from the main article applied to 2 systems
-- says:
-- ∀x_1, x_2:
--     x_1 ∩ x_2 = ∅ →
--          ∀A,U_1,U_2: {A}
--              x_1:=U_1 x_1, x_2:=U_2 x_2
--              {(U_1⊗U_2)A(adj(U_1⊗U_2))}
-- here x_1, x_2 are variables that can be interpreted as
-- subsystems of quantum registry
-- It is obvious from the rule that A acts in the space
-- x_1∪x_2
-- Ax.UTFP2 means that the rule is applied to 2 systems,
-- _1_1 means that both systems are 1 qubit
| Ax.UTFP2_1_1
    -- first system
    (i1: Fin 3)
    -- second system
    (i2: Fin 3)
    -- condition that systems are disjoint
    (disj: ¬(i1 = i2))
    (A: OP.oi2 (min i1 i2) (max i1 i2) (by f2 i1 i2))
    (U_1: OP.oi1 i1)(un_1: HC.isUnitary U_1)
    (U_2: OP.oi1 i2)(un_2: HC.isUnitary U_2):
      Inf (Cond.c2 A)
          (Prog.seq
            (Prog.gate1 U_1 un_1)
            (Prog.gate1 U_2 un_2)
          )
          (by
             let pr:Prop := i1 < i2
             by_cases pr
             {
                have less:i1 < i2 := by aesop
                simp [less, min, max] at A
                exact Cond.c2 (
                              (TO.tpo1o1i i1 i2 less U_1 U_2) •
                              A •
                              (HC.adj (TO.tpo1o1i i1 i2 less U_1 U_2))
                              )
             }
             {
                have less:i2 < i1 := by omega
                have s:¬(i1 < i2) := by aesop
                simp [s, min, max] at A
                exact Cond.c2 (
                              (TO.tpo1o1i i2 i1 less U_2 U_1) •
                              A •
                             (HC.adj (TO.tpo1o1i i2 i1 less U_2 U_1))
                             )
             }
           )

| Ax.UTFP2_2_1
    -- first system
    (i1 i2)(ord: i1 < i2)
    -- second system
    (j: Fin 3)
    -- system disjointness propositions
    (neq1: ¬(j=i1))(neq2: ¬(j=i2))
    (A: OP.o3)
    (U_1: OP.oi2 i1 i2 ord)(un_1: HC.isUnitary U_i)
    (U_2: OP.oi1 j)(un_2: HC.isUnitary U_2):
      Inf (Cond.c3 A)
          (Prog.seq
           (Prog.gate2 U_i un_i)
           (Prog.gate1 U_j un_j)
          )
           (Cond.c3 (
                    (TO.tpo2o1i i1 i2 ord j neq1 neq2 U_i U_j) •
                    A •
                    (HC.adj (TO.tpo2o1i i1 i2 ord j neq1 neq2 U_i U_j))
           ))

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
