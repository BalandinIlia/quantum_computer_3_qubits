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
--     {A} Prog.gate U {U ∘ₗ A ∘ₗ U^}
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
--         {(U_1⊗U_2)∘ₗA∘ₗ(U_1⊗U_2)^}
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
--         {(U_1⊗U_2⊗U_3)∘ₗA∘ₗ(U_1⊗U_2⊗U_3)^}
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

namespace QWhile

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
-- These inference rules are translated from the intermediate
-- language. Each string in the input correspond to one
-- term in the intermediate language:
inductive InfRules: Cond → Prog → Cond → Prop

-- rule for skip program
-- Here we do an exception, since the rule is trivial and,
-- in fact does not require intermediate langauge in order
-- to be formalized in Lean
| Ax.Sk(A: Cond): InfRules A Prog.skip A

-- Ax.UTF for case when x is a 1-qubit system
| Ax.UTF1
    (x: Fin 3)
    (U: (OP.oi1 x))(un: HC.isUnitary U)
    (A: (OP.oi1 x)):
InfRules (Cond.c1 A)
         (Prog.gate1 U un)
         (Cond.c1 (U ∘ₗ A ∘ₗ (HC.adj U)))

-- Ax.UTF for case when x is a 2-qubit system
| Ax.UTF2
    (x_1 x_2: Fin 3)(ord: x_1 < x_2)
    (U: (OP.oi2 x_1 x_2 ord))(un: HC.isUnitary U)
    (A: (OP.oi2 x_1 x_2 ord)):
InfRules (Cond.c2 A)
         (Prog.gate2 U un)
         (Cond.c2 (U ∘ₗ A ∘ₗ(HC.adj U)))

-- Ax.UTF for case when x is a 3-qubit system
| Ax.UTF3
    -- In this string we formalize x, but for this case it is empty.
    (U: OP.o3)(un: HC.isUnitary U)
    (A: OP.o3):
InfRules (Cond.c3 A)
         (Prog.gate3 U un)
         (Cond.c3 (U ∘ₗ A ∘ₗ (HC.adj U)))

-- Ax.Inf for case when S and x are both 1-qubit systems
| Ax.Inf_1_1
    (S: Fin 3)
    (x: Fin 3)
    (disj: ¬(S = x))
    (A_S: OP.oi1 S)
    (t: StateReg1Ind x)(norm: (IP.f t t) = 1):
InfRules (Cond.c1 A_S)
         (Prog.ass1 t norm)
         (by
            let pr := (S < x)
            by_cases pr
            exact Cond.c2 (TO.tpo1o1i S x (by aesop) A_S (OP t t))
            exact Cond.c2 (TO.tpo1o1i x S (by omega) (OP t t) A_S)
         )

| Ax.Inf_2_1
    (S_1 S_2: Fin 3)(ord: S_1 < S_2)
    (x: Fin 3)
    (disj1: ¬(x = S_1))(disj2: ¬(x = S_2))
    (A_S: OP.oi2 S_1 S_2 ord)
    (t: StateReg1Ind x)(norm: (IP.f t t) = 1):
InfRules (Cond.c2 A_S)
         (Prog.ass1 t norm)
         (Cond.c3 (TO.tpo2o1i S_1 S_2 ord x disj1 disj2 A_S (OP t t)))

| Ax.Inf_1_2
    (S: Fin 3)
    (x_1 x_2: Fin 3)(ord: x_1 < x_2)
    (disj1: ¬(S = x_1))(disj2: ¬(S = x_2))
    (A_S: OP.oi1 S)
    (t: StateReg2Ind x_1 x_2 ord)(norm: (IP.f t t) = 1):
InfRules (Cond.c1 A_S)
         (Prog.ass2 t norm)
         (Cond.c3 (TO.tpo2o1i x_1 x_2 ord S disj1 disj2 (OP t t) A_S))

| R.SC: ∀A B C: Cond, ∀S1 S2: Prog, InfRules A S1 B →
                                    InfRules B S2 C →
                                    InfRules A (Prog.seq S1 S2) C

-- Ax.UTFP2 for 1-qubit and 1-qubit systems
| Ax.UTFP2_1_1
    (x_1: Fin 3)
    (x_2: Fin 3)
    (disj: ¬(x_1 = x_2))
    (U_1: OP.oi1 x_1)(un_1: HC.isUnitary U_1)
    (U_2: OP.oi1 x_2)(un_2: HC.isUnitary U_2)
    (A: OP.oi2 (min x_1 x_2) (max x_1 x_2) (by f2 x_1 x_2)):
InfRules (Cond.c2 A)
         (Prog.seq
            (Prog.gate1 U_1 un_1)
            (Prog.gate1 U_2 un_2)
         )
         (by
            let pr:Prop := x_1 < x_2
            by_cases pr
            {
               have less: x_1 < x_2 := by aesop
               simp [less, min, max] at A
               let tpU := TO.tpo1o1i x_1 x_2 less U_1 U_2
               exact Cond.c2 (tpU ∘ₗ A ∘ₗ (HC.adj tpU))
            }
            {
               have less: x_2 < x_1 := by omega
               have s:¬(x_1 < x_2) := by aesop
               simp [s, min, max] at A
               let tpU := TO.tpo1o1i x_2 x_1 less U_2 U_1
               exact Cond.c2 (tpU ∘ₗ A ∘ₗ (HC.adj tpU))
            }
         )

| Ax.UTFP2_2_1
    (x_1_1 x_1_2: Fin 3)(ord: x_1_1 < x_1_2)
    (x_2: Fin 3)
    (disj1: ¬(x_2=x_1_1))(disj2: ¬(x_2=x_1_2))
    (U_1: OP.oi2 x_1_1 x_1_2 ord)(un_1: HC.isUnitary U_1)
    (U_2: OP.oi1 x_2)(un_2: HC.isUnitary U_2)
    (A: OP.o3):
InfRules (Cond.c3 A)
         (Prog.seq
            (Prog.gate2 U_1 un_1)
            (Prog.gate1 U_2 un_2)
         )
         (Cond.c3 (by
                     let tpU := TO.tpo2o1i x_1_1 x_1_2 ord x_2 disj1 disj2 U_1 U_2
                     exact tpU ∘ₗ A ∘ₗ (HC.adj tpU)
                  )
         )

| Ax.UTFP2_1_2
    (x_1: Fin 3)
    (x_2_1 x_2_2: Fin 3)(ord: x_2_1 < x_2_2)
    (disj1: ¬(x_1=x_2_1))(disj2: ¬(x_1=x_2_2))
    (U_1: OP.oi1 x_1)(un_1: HC.isUnitary U_1)
    (U_2: OP.oi2 x_2_1 x_2_2 ord)(un_2: HC.isUnitary U_2)
    (A: OP.o3):
InfRules (Cond.c3 A)
         (Prog.seq
            (Prog.gate1 U_1 un_1)
            (Prog.gate2 U_2 un_2)
         )
         (Cond.c3 (by
                     let tpU := TO.tpo2o1i x_2_1 x_2_2 ord x_1 disj1 disj2 U_2 U_1
                     exact tpU ∘ₗ A ∘ₗ (HC.adj tpU)
                  )
         )

| Ax.UTFP3
    (x_1: Fin 3)
    (x_2: Fin 3)
    (x_3: Fin 3)
    (disj1: ¬(x_1 = x_2))(disj2: ¬(x_1 = x_3))(disj3: ¬(x_2 = x_3))
    (U_1: OP.oi1 x_1)(un_1: HC.isUnitary U_1)
    (U_2: OP.oi1 x_2)(un_2: HC.isUnitary U_2)
    (U_3: OP.oi1 x_3)(un_3: HC.isUnitary U_3)
    (A: OP.o3):
InfRules (Cond.c3 A)
         (Prog.seq
            (Prog.seq (Prog.gate1 U_1 un_1)
                      (Prog.gate1 U_2 un_2)
            )
            (Prog.gate1 U_3 un_3)
         )
         (Cond.c3 (by
                     let tpU: OP.o3 := by
                       let pr: Prop := x_1 < x_2
                       by_cases pr
                       exact TO.tpo2o1i x_1
                                        x_2
                                        (by f2 x_1 x_2)
                                        x_3
                                        (by f2 x_1 x_2)
                                        (by f2 x_1 x_2)
                                        (TO.tpo1o1i x_1 x_2 (by f2 x_1 x_2) U_1 U_2)
                                        U_3
                       exact TO.tpo2o1i x_2
                                        x_1
                                        (by f2 x_1 x_2)
                                        x_3
                                        (by f2 x_1 x_2)
                                        (by f2 x_1 x_2)
                                        (TO.tpo1o1i x_2 x_1 (by f2 x_1 x_2) U_2 U_1)
                                        U_3
                     exact tpU ∘ₗ A ∘ₗ (HC.adj tpU)
                  )
         )

-- Ax.InFP2 rule for two 1-qubit systems
| Ax.InFP2_1_1
    (x_1: Fin 3)
    (x_2: Fin 3)
    (disj: ¬(x_1 = x_2))
    (t_1: StateReg1Ind x_1)(n_1: IP.f t_1 t_1 = 1)
    (t_2: StateReg1Ind x_2)(n_2: IP.f t_2 t_2 = 1):
InfRules (Cond.c0)
         (Prog.seq (Prog.ass1 t_1 n_1) (Prog.ass1 t_2 n_2))
         (by
            let pr: Prop := x_1 < x_2
            by_cases pr
            exact Cond.c2 (TO.tpo1o1i x_1 x_2 (by f2 x_1 x_2) (OP t_1 t_1) (OP t_2 t_2))
            exact Cond.c2 (TO.tpo1o1i x_2 x_1 (by f2 x_1 x_2) (OP t_2 t_2) (OP t_1 t_1))
         )

-- Ax.InFP2 rule for 2-qubit system and 1-qubit system
| Ax.InFP2_2_1
    (x_1_1: Fin 3)(x_1_2: Fin 3)(ord: x_1_1 < x_1_2)
    (x_2: Fin 3)
    (disj1: ¬(x_1_1 = x_2))(disj1: ¬(x_1_2 = x_2))
    (t_1: StateReg2Ind x_1_1 x_1_2 ord)(n_1: IP.f t_1 t_1 = 1)
    (t_2: StateReg1Ind x_2)(n_2: IP.f t_2 t_2 = 1):
InfRules (Cond.c0)
         (Prog.seq (Prog.ass2 t_1 n_1) (Prog.ass1 t_2 n_2))
         (Cond.c3 (TO.tpo2o1i x_1_1
                              x_1_2
                              ord
                              x_2
                              (by f2 x_1_1 x_2)
                              (by f2 x_1_2 x_2)
                              (OP t_1 t_1)
                              (OP t_2 t_2)
                  )
         )

-- Ax.InFP2 rule for 1-qubit system and 2-qubit system
| Ax.InFP2_1_2
    (x_1: Fin 3)
    (x_2_1: Fin 3)(x_2_2: Fin 3)(ord: x_2_1 < x_2_2)
    (disj1: ¬(x_1 = x_2_1))(disj1: ¬(x_1 = x_2_2))
    (t_1: StateReg1Ind x_1)(n_1: IP.f t_1 t_1 = 1)
    (t_2: StateReg2Ind x_2_1 x_2_2 ord)(n_2: IP.f t_2 t_2 = 1):
InfRules (Cond.c0)
         (Prog.seq (Prog.ass1 t_1 n_1) (Prog.ass2 t_2 n_2))
         (Cond.c3 (TO.tpo2o1i x_2_1
                              x_2_2
                              ord
                              x_1
                              (by f2 x_1 x_2_1)
                              (by f2 x_1 x_2_2)
                              (OP t_2 t_2)
                              (OP t_1 t_1)
                  )
         )

| Ax.inFP3
    (x_1: Fin 3)
    (x_2: Fin 3)
    (x_3: Fin 3)
    (disj1: ¬(x_1 = x_2))(disj2: ¬(x_1 = x_3))(disj3: ¬(x_2 = x_3))
    (t_1: StateReg1Ind x_1)(n_1: IP.f t_1 t_1 = 1)
    (t_2: StateReg1Ind x_2)(n_2: IP.f t_2 t_2 = 1)
    (t_3: StateReg1Ind x_3)(n_3: IP.f t_3 t_3 = 1):
InfRules (Cond.c0)
         (Prog.seq (Prog.seq (Prog.ass1 t_1 n_1) (Prog.ass1 t_2 n_2))
                   (Prog.ass1 t_3 n_3)
         )
         (Cond.c3 (by
                     let pr: Prop := x_1 < x_2
                     by_cases pr
                     exact TO.tpo2o1i x_1
                                      x_2
                                      (by f2 x_1 x_2)
                                      x_3
                                      (by f2 x_1 x_3)
                                      (by f2 x_2 x_3)
                                      (TO.tpo1o1i x_1 x_2 (by f2 x_1 x_2) (OP t_1 t_1) (OP t_2 t_2))
                                      (OP t_3 t_3)
                     exact TO.tpo2o1i x_2
                                      x_1
                                      (by f2 x_1 x_2)
                                      x_3
                                      (by f2 x_1 x_3)
                                      (by f2 x_2 x_3)
                                      (TO.tpo1o1i x_2 x_1 (by f2 x_1 x_2) (OP t_2 t_2) (OP t_1 t_1))
                                      (OP t_3 t_3)
                  )
         )

-- R.CC.P for 2 1-qubit systems
| R.CC.P_1_1
    (N: ℕ)(pos: N > 0)
    (x_A: Fin 3)
    (x_B: Fin 3)
    (A: Fin N → (OP.oi1 x_A))
    (B: Fin N → (OP.oi1 x_B))
    (lam: Fin N → ℝ)
    (C: Prog)
    (pr_lam_pos: ∀i: Fin N, lam i ≥ 0)
    (pr_lam_sum: FS.fs lam ≤ 1)
    (hoar: ∀i: Fin N, InfRules (Cond.c1 (A i)) C (Cond.c1 (B i))):
InfRules (Cond.c1 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (A i))))
         C
         (Cond.c1 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (B i))))

-- R.CC.P for 1-qubit system and 2-qubit system
| R.CC.P_1_2
    (N: ℕ)(pos: N > 0)
    (x_A: Fin 3)
    (x_B_1: Fin 3)(x_B_2: Fin 3)(ordB: x_B_1 < x_B_2)
    (A: Fin N → (OP.oi1 x_A))
    (B: Fin N → (OP.oi2 x_B_1 x_B_2 ordB))
    (lam: Fin N → ℝ)
    (C: Prog)
    (pr_lam_pos: ∀i: Fin N, lam i ≥ 0)
    (pr_lam_sum: FS.fs lam ≤ 1)
    (hoar: ∀i: Fin N, InfRules (Cond.c1 (A i)) C (Cond.c2 (B i))):
InfRules (Cond.c1 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (A i))))
         C
         (Cond.c2 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (B i))))

-- R.CC.P for 1-qubit system and 3-qubit system
| R.CC.P_1_3
    (N: ℕ)(pos: N > 0)
    (x_A: Fin 3)
    -- no arguments for B system, since it is the entire quantum registry
    (A: Fin N → (OP.oi1 x_A))
    (B: Fin N → OP.o3)
    (lam: Fin N → ℝ)
    (C: Prog)
    (pr_lam_pos: ∀i: Fin N, lam i ≥ 0)
    (pr_lam_sum: FS.fs lam ≤ 1)
    (hoar: ∀i: Fin N, InfRules (Cond.c1 (A i)) C (Cond.c3 (B i))):
InfRules (Cond.c1 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (A i))))
         C
         (Cond.c3 (FS.fs (fun i: Fin N => ((lam i):ℂ) • (B i))))

-- R.El rule for 1-qubit system and 1-qubit system
| R.El_1_1
    (S_A: Fin 3)
    (S: Fin 3)
    -- here we make a trick and cover all possible B systems in one rule
    (disj: ¬(S = S_A))
    (A_S_A: OP.oi1 S_A)
    (C: Prog)
    (B: Cond)
    (hoar: InfRules (Cond.c1 A_S_A) C B):
InfRules (by
            let pr:Prop := S_A < S
            by_cases pr
            exact Cond.c2 (TO.tpo1o1i S_A S (by f2 S_A S) A_S_A (OP.idoi1 S))
            exact Cond.c2 (TO.tpo1o1i S S_A (by f2 S_A S) (OP.idoi1 S) A_S_A)
         )
         C
         B

-- R.El rule for 2-qubit system and 1-qubit system
| R.El_2_1
    (S_A_1 S_A_2: Fin 3)(ord: S_A_1 < S_A_2)
    (S: Fin 3)
    -- here we make a trick and cover all possible B systems in one rule
    (disj1: ¬(S = S_A_1))(disj1: ¬(S = S_A_2))
    (A_S_A: OP.oi2 S_A_1 S_A_2 ord)
    (C: Prog)
    (B: Cond)
    (hoar: InfRules (Cond.c2 A_S_A) C B):
InfRules (Cond.c3 (TO.tpo2o1i S_A_1
                              S_A_2
                              ord
                              S
                              (by f2 S S_A_1)
                              (by f2 S S_A_2)
                              A_S_A
                              (OP.idoi1 S)
                  )
         )
         C
         B

-- R.El rule for 2-qubit system and 1-qubit system
| R.El_1_2
    (S_A: Fin 3)
    (S_1 S_2: Fin 3)(ord: S_1 < S_2)
    -- here we make a trick and cover all possible B systems in one rule
    (disj1: ¬(S_1 = S_A))(disj1: ¬(S_2 = S_A))
    (A_S_A: OP.oi1 S_A)
    (C: Prog)
    (B: Cond)
    (hoar: InfRules (Cond.c1 A_S_A) C B):
InfRules (Cond.c3 (TO.tpo2o1i S_1
                              S_2
                              ord
                              S_A
                              (by f2 S_1 S_A)
                              (by f2 S_2 S_A)
                              (OP.idoi2 S_1 S_2 ord)
                              A_S_A
                  )
         )
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
InfRules (CondSt sBeg) prog (CondSt sFin)
