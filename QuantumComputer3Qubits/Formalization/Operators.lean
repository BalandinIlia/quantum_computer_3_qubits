import QuantumComputer3Qubits.Formalization.RegistryState
import QuantumComputer3Qubits.Tests.StateExamples
import QuantumComputer3Qubits.Formalization.FiniteSum
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

lemma hjk(op1 op2: o3):
(op1 SE.s000 = op2 SE.s000) →
(op1 SE.s001 = op2 SE.s001) →
(op1 SE.s010 = op2 SE.s010) →
(op1 SE.s011 = op2 SE.s011) →
(op1 SE.s100 = op2 SE.s100) →
(op1 SE.s101 = op2 SE.s101) →
(op1 SE.s110 = op2 SE.s110) →
(op1 SE.s111 = op2 SE.s111) →
op1 = op2 := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  have t:∀s: StateReg3, op1 s = op2 s := by
    intro s
    let ob: OrthonormalBasis StateReg3 := inferInstance
    let repr := FS.basisReprAx 8 (by omega) ob.basis s
    simp [FS.basisRepr] at repr
    simp [FS.fs, FS.sumPartial] at repr
    simp [FS.sumPartial.eq_def] at repr
    rw [repr]
    clear repr
    simp
    have cor: ∀i: Fin 8, op1 (ob.basis i) = op2 (ob.basis i) := by
      /-intro i
      fin_cases i
      {
        generalize r:ob.basis 0=b
        simp [r]
        simp [OB.OrthonormalBasisInstDim8, StateReg3, StateReg2Ind, OB.OrthonormalBasisImpl, QubitInd, ob] at b r
        let x:=X1.a
        #check b
      }
      let rt:=ob.basis 0
      simp [OB.OrthonormalBasisInstDim8, StateReg3, StateReg2Ind] at rt-/
      sorry
    generalize r10: op1 (OrthonormalBasis.basis 0) = v10
    generalize r20: op2 (OrthonormalBasis.basis 0) = v20
    generalize r11: op1 (OrthonormalBasis.basis 1) = v11
    generalize r21: op2 (OrthonormalBasis.basis 1) = v21
    generalize r12: op1 (OrthonormalBasis.basis 2) = v12
    generalize r22: op2 (OrthonormalBasis.basis 2) = v22
    generalize r13: op1 (OrthonormalBasis.basis 3) = v13
    generalize r23: op2 (OrthonormalBasis.basis 3) = v23
    generalize r14: op1 (OrthonormalBasis.basis 4) = v14
    generalize r24: op2 (OrthonormalBasis.basis 4) = v24
    generalize r15: op1 (OrthonormalBasis.basis 5) = v15
    generalize r25: op2 (OrthonormalBasis.basis 5) = v25
    generalize r16: op1 (OrthonormalBasis.basis 6) = v16
    generalize r26: op2 (OrthonormalBasis.basis 6) = v26
    generalize r17: op1 (OrthonormalBasis.basis 7) = v17
    generalize r27: op2 (OrthonormalBasis.basis 7) = v27
    have o0:v10=v20 := by aesop
    have o1:v11=v21 := by aesop
    have o2:v12=v22 := by aesop
    have o3:v13=v23 := by aesop
    have o4:v14=v24 := by aesop
    have o5:v15=v25 := by aesop
    have o6:v16=v26 := by aesop
    have o7:v17=v27 := by aesop
    aesop
  aesop

-- oi means "operator indexed"
@[reducible]
def oi1(i1: Fin 3):Type :=
  (StateReg1Ind i1) →ₗ[ℂ] (StateReg1Ind i1)

@[reducible]
def oi2(i1 i2: Fin 3)(ord: (i1 < i2)):Type :=
  (StateReg2Ind i1 i2 ord) →ₗ[ℂ] (StateReg2Ind i1 i2 ord)
