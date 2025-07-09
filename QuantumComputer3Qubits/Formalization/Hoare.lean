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

namespace Hoare

inductive H where
| cond1(i:Fin 3):                     (OP.oi1 i) → H
| cond2(i1 i2: Fin 3)(ord: i1 < i2):  (OP.oi2 i1 i2 ord) → H
| cond3:                              OP.o3 → H

inductive Prog where
| skip:                              Prog
| ass1(i:Fin 3):                     StateReg1Ind i → Prog
| ass2(i1 i2: Fin 3)(ord: i1 < i2):  StateReg2Ind i1 i2 ord → Prog
| ass3:                              StateReg3 → Prog
| gate1(i:Fin 3):                    OP.oi1 i → Prog
| gate2(i1 i2: Fin 3)(o: i1 < i2):   OP.oi2 i1 i2 o → Prog
| gate3:                             OP.o3 → Prog
| meas1:                             Fin 3 → Prog → Prog → Prog
| seq:                               Prog → Prog → Prog

noncomputable
instance inth(i: Fin 3): OrthonormalBasis (StateReg1Ind i) :=
match i with
| 0 => inferInstance
| 1 => inferInstance
| 2 => inferInstance

noncomputable
instance intth(i1 i2: Fin 3)(ord: i1 < i2): OrthonormalBasis (StateReg2Ind i1 i2 ord) :=
match i1, i2 with
| 0, 0 => inferInstance
| 0, 1 => inferInstance
| 0, 2 => inferInstance
| 1, 0 => inferInstance
| 1, 1 => inferInstance
| 1, 2 => inferInstance
| 2, 0 => inferInstance
| 2, 1 => inferInstance
| 2, 2 => inferInstance

inductive Hoar: H → Prog → H → Prop
| Ax.Sk:   ∀h: H, Hoar h Prog.skip h
| Ax.UTF1(i: Fin 3):
    ∀op tr: (OP.oi1 i),
      Hoar (H.cond1 i op)
           (Prog.gate1 i tr)
           (H.cond1 i ((tr • op)•(HC.adj tr)))
| Ax.UTF2(i1 i2: Fin 3)(ord: i1 < i2):
    ∀op tr: (OP.oi2 i1 i2 ord),
      Hoar (H.cond2 i1 i2 ord op)
           (Prog.gate2 i1 i2 ord tr)
           (H.cond2 i1 i2 ord ((tr • op)•(HC.adj tr)))
| Ax.Inf_1_1(i1 i2: Fin 3)(ord: i1 < i2):
    ∀op: OP.oi1 i1, ∀s: StateReg1Ind i2,
      Hoar (H.cond1 i1 op)
           (Prog.ass1 i2 s)
           (H.cond2 i1 i2 ord
              (TO.tpo1o1i i1 i2 ord op (OP s s)))
| Ax.Inf_1_1_(i1 i2: Fin 3)(ord: i1 > i2):
    ∀op: OP.oi1 i1, ∀s: StateReg1Ind i2,
      Hoar (H.cond1 i1 op)
           (Prog.ass1 i2 s)
           (H.cond2 i2 i1 (by aesop)
              (TO.tpo1o1i i2 i1 ord (OP s s) op))
| Ax.Inf_2_1(i1 i2: Fin 3)(ord: i1 < i2)(i3: Fin 3)(neq1: ¬(i1=i3))(neq2: ¬(i2=i3)):
    ∀op: OP.oi2 i1 i2 ord, ∀s: StateReg1Ind i3,
      Hoar (H.cond2 i1 i2 ord op)
           (Prog.ass1 i3 s)
           (H.cond3 (TO.tpo2o1i i1 i2 ord i3 (by aesop) (by aesop) op (OP s s)))
| Ax.Inf_1_2(i1 i2: Fin 3)(ord: i1 < i2)(i3: Fin 3)(neq1: ¬(i1=i3))(neq2: ¬(i2=i3)):
    ∀op: OP.oi1 i3, ∀s: StateReg2Ind i1 i2 ord,
      Hoar (H.cond1 i3 op)
           (Prog.ass2 i1 i2 ord s)
           (H.cond3 (TO.tpo2o1i i1 i2 ord i3 (by aesop) (by aesop) (OP s s) op))
| R.SC: ∀A B C: H, ∀S1 S2: Prog, Hoar A S1 B → Hoar B S2 C → Hoar A (Prog.seq S1 S2) C
