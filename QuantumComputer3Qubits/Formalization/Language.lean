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

inductive Cond where
| c1{i:Fin 3}:                     (OP.oi1 i) → Cond
| c2{i1 i2: Fin 3}{ord: i1 < i2}:  (OP.oi2 i1 i2 ord) → Cond
| c3:                              OP.o3 → Cond

inductive Prog where
| skip:                              Prog
| ass1{i:Fin 3}:                     StateReg1Ind i → Prog
| ass2{i1 i2: Fin 3}{ord: i1 < i2}:  StateReg2Ind i1 i2 ord → Prog
| ass3:                              StateReg3 → Prog
| gate1{i:Fin 3}:                    OP.oi1 i → Prog
| gate2{i1 i2: Fin 3}{o: i1 < i2}:   OP.oi2 i1 i2 o → Prog
| gate3:                             OP.o3 → Prog
| seq:                               Prog → Prog → Prog

inductive Inf: Cond → Prog → Cond → Prop
| Ax.Sk:   ∀h: Cond, Inf h Prog.skip h
| Ax.UTF1(i: Fin 3):
    ∀op tr: (OP.oi1 i),
      Inf (Cond.c1 op)
          (Prog.gate1 tr)
          (Cond.c1 (LinearMap.comp (LinearMap.comp tr op) (HC.adj tr)))
| Ax.UTF2(i1 i2: Fin 3)(ord: i1 < i2):
    ∀op tr: (OP.oi2 i1 i2 ord),
      Inf (Cond.c2 op)
          (Prog.gate2 tr)
          (Cond.c2 ((tr • op)•(HC.adj tr)))
| Ax.Inf_1_1(i1 i2: Fin 3)(ord: i1 < i2):
    ∀op: OP.oi1 i1, ∀s: StateReg1Ind i2,
      Inf (Cond.c1 op)
          (Prog.ass1 s)
          (Cond.c2 (TO.tpo1o1i i1 i2 ord op (OP s s)))
| Ax.Inf_1_1_(i1 i2: Fin 3)(ord: i1 > i2):
    ∀op: OP.oi1 i1, ∀s: StateReg1Ind i2,
      Inf (Cond.c1 op)
          (Prog.ass1 s)
          (Cond.c2 (TO.tpo1o1i i2 i1 ord (OP s s) op))
| Ax.Inf_2_1(i1 i2: Fin 3)(ord: i1 < i2)(i3: Fin 3)(neq1: ¬(i1=i3))(neq2: ¬(i2=i3)):
    ∀op: OP.oi2 i1 i2 ord, ∀s: StateReg1Ind i3,
      Inf (Cond.c2 op)
          (Prog.ass1 s)
          (Cond.c3 (TO.tpo2o1i i1 i2 ord i3 (by aesop) (by aesop) op (OP s s)))
| Ax.Inf_1_2(i1 i2: Fin 3)(ord: i1 < i2)(i3: Fin 3)(neq1: ¬(i1=i3))(neq2: ¬(i2=i3)):
    ∀op: OP.oi1 i3, ∀s: StateReg2Ind i1 i2 ord,
      Inf (Cond.c1 op)
          (Prog.ass2 s)
          (Cond.c3 (TO.tpo2o1i i1 i2 ord i3 (by aesop) (by aesop) (OP s s) op))
| R.SC: ∀A B C: Cond, ∀S1 S2: Prog, Inf A S1 B → Inf B S2 C → Inf A (Prog.seq S1 S2) C
