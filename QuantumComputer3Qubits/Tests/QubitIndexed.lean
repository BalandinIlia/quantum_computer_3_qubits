import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.QubitIndexed

namespace Test_QubitIndexed

-- check that module can be synthesized for each indexed qubit
#synth Module ℂ (QubitInd 0)
#synth Module ℂ (QubitInd 1)
#synth Module ℂ (QubitInd 2)

--
noncomputable
def QZeroImage(i: Fin 3) := LinearEquiv.symm (isoQubitIndQubitBase i) QZero

noncomputable
def QOneImage(i: Fin 3) := LinearEquiv.symm (isoQubitIndQubitBase i) QOne

-- check that image of QZero behaves as expected
theorem testQZeroImage:
  (QZeroImage 0 X1.a = 1) ∧
  (QZeroImage 0 X1.b = 0) ∧
  (QZeroImage 1 X2.a = 1) ∧
  (QZeroImage 1 X2.b = 0) ∧
  (QZeroImage 2 X3.a = 1) ∧
  (QZeroImage 2 X3.b = 0) := by
  simp [QZeroImage, isoQubitIndQubitBase, QZero]

-- check that image of QOne behaves as expected
theorem testQOneImage:
  (QOneImage 0 X1.a = 0) ∧
  (QOneImage 0 X1.b = 1) ∧
  (QOneImage 1 X2.a = 0) ∧
  (QOneImage 1 X2.b = 1) ∧
  (QOneImage 2 X3.a = 0) ∧
  (QOneImage 2 X3.b = 1) := by
  simp [QOneImage, isoQubitIndQubitBase, QOne]

-- check that inner product is defined for indexed qubits
#synth IP (QubitInd 0)
#synth IP (QubitInd 1)
#synth IP (QubitInd 2)

theorem testIP1: ∀i: Fin 3, IP.f (QZeroImage i) (QZeroImage i) = 1 := by
  intro i
  fin_cases i
  {
    have eq: (QZeroImage 0) = fun x:X1 => match x with | X1.a => 1 | X1.b => 0 := by
      simp [QZeroImage, isoQubitIndQubitBase, QZero]
      aesop
    simp
    rw [eq]
    clear eq
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl:
        (isoQubitIndQubitBase 0)
        (fun x:X1 => match x with | X1.a => 1 | X1.b => 0) = f
    have eq0: f 0 = 1 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    have eq1: f 1 = 0 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    simp [eq0, eq1]
  }
  {
    have eq: (QZeroImage 1) = fun x:X2 => match x with | X2.a => 1 | X2.b => 0 := by
      simp [QZeroImage, isoQubitIndQubitBase, QZero]
      aesop
    simp
    rw [eq]
    clear eq
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl:
        (isoQubitIndQubitBase 1)
        (fun x:X2 => match x with | X2.a => 1 | X2.b => 0) = f
    have eq0: f 0 = 1 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    have eq1: f 1 = 0 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    simp [eq0, eq1]
  }
  {
    have eq: (QZeroImage 2) = fun x:X3 => match x with | X3.a => 1 | X3.b => 0 := by
      simp [QZeroImage, isoQubitIndQubitBase, QZero]
      aesop
    simp
    rw [eq]
    clear eq
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl:
        (isoQubitIndQubitBase 2)
        (fun x:X3 => match x with | X3.a => 1 | X3.b => 0) = f
    have eq0: f 0 = 1 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    have eq1: f 1 = 0 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    simp [eq0, eq1]
  }

theorem testIP2: ∀i: Fin 3, IP.f (QZeroImage i) (QOneImage i) = 0 := by
  intro i
  fin_cases i
  {
    have eq0: (QZeroImage 0) = fun x:X1 => match x with | X1.a => 1 | X1.b => 0 := by
      simp [QZeroImage, isoQubitIndQubitBase, QZero]
      aesop
    have eq1: (QOneImage 0) = fun x:X1 => match x with | X1.a => 0 | X1.b => 1 := by
      simp [QOneImage, isoQubitIndQubitBase, QOne]
      aesop
    simp
    rw [eq0, eq1]
    clear eq0 eq1
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl1:
        (isoQubitIndQubitBase 0)
        (fun x:X1 => match x with | X1.a => 0 | X1.b => 1) = f1
    generalize repl2:
        (isoQubitIndQubitBase 0)
        (fun x:X1 => match x with | X1.a => 1 | X1.b => 0) = f2
    have eq0: f1 0 = 0 := by
      simp [Eq.symm repl1, isoQubitIndQubitBase]
    have eq1: f1 1 = 1 := by
      simp [Eq.symm repl1, isoQubitIndQubitBase]
    have eq2: f2 1 = 0 := by
      simp [Eq.symm repl2, isoQubitIndQubitBase]
    have eq3: f2 0 = 1 := by
      simp [Eq.symm repl2, isoQubitIndQubitBase]
    simp [eq0, eq1, eq2, eq3]
  }
  {
    have eq0: (QZeroImage 1) = fun x:X2 => match x with | X2.a => 1 | X2.b => 0 := by
      simp [QZeroImage, isoQubitIndQubitBase, QZero]
      aesop
    have eq1: (QOneImage 1) = fun x:X2 => match x with | X2.a => 0 | X2.b => 1 := by
      simp [QOneImage, isoQubitIndQubitBase, QOne]
      aesop
    simp
    rw [eq0, eq1]
    clear eq0 eq1
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl1:
        (isoQubitIndQubitBase 1)
        (fun x:X2 => match x with | X2.a => 0 | X2.b => 1) = f1
    generalize repl2:
        (isoQubitIndQubitBase 1)
        (fun x:X2 => match x with | X2.a => 1 | X2.b => 0) = f2
    have eq0: f1 0 = 0 := by
      simp [Eq.symm repl1, isoQubitIndQubitBase]
    have eq1: f1 1 = 1 := by
      simp [Eq.symm repl1, isoQubitIndQubitBase]
    have eq2: f2 1 = 0 := by
      simp [Eq.symm repl2, isoQubitIndQubitBase]
    have eq3: f2 0 = 1 := by
      simp [Eq.symm repl2, isoQubitIndQubitBase]
    simp [eq0, eq1, eq2, eq3]
  }
  {
    have eq0: (QZeroImage 2) = fun x:X3 => match x with | X3.a => 1 | X3.b => 0 := by
      simp [QZeroImage, isoQubitIndQubitBase, QZero]
      aesop
    have eq1: (QOneImage 2) = fun x:X3 => match x with | X3.a => 0 | X3.b => 1 := by
      simp [QOneImage, isoQubitIndQubitBase, QOne]
      aesop
    simp
    rw [eq0, eq1]
    clear eq0 eq1
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl1:
        (isoQubitIndQubitBase 2)
        (fun x:X3 => match x with | X3.a => 0 | X3.b => 1) = f1
    generalize repl2:
        (isoQubitIndQubitBase 2)
        (fun x:X3 => match x with | X3.a => 1 | X3.b => 0) = f2
    have eq0: f1 0 = 0 := by
      simp [Eq.symm repl1, isoQubitIndQubitBase]
    have eq1: f1 1 = 1 := by
      simp [Eq.symm repl1, isoQubitIndQubitBase]
    have eq2: f2 1 = 0 := by
      simp [Eq.symm repl2, isoQubitIndQubitBase]
    have eq3: f2 0 = 1 := by
      simp [Eq.symm repl2, isoQubitIndQubitBase]
    simp [eq0, eq1, eq2, eq3]
  }

theorem testIP3: ∀i: Fin 3, IP.f (QOneImage i) (QOneImage i) = 1 := by
  intro i
  fin_cases i
  {
    have eq: (QOneImage 0) = fun x:X1 => match x with | X1.a => 0 | X1.b => 1 := by
      simp [QOneImage, isoQubitIndQubitBase, QOne]
      aesop
    simp
    rw [eq]
    clear eq
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl:
        (isoQubitIndQubitBase 0)
        (fun x:X1 => match x with | X1.a => 0 | X1.b => 1) = f
    have eq0: f 0 = 0 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    have eq1: f 1 = 1 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    simp [eq0, eq1]
  }
  {
    have eq: (QOneImage 1) = fun x:X2 => match x with | X2.a => 0 | X2.b => 1 := by
      simp [QOneImage, isoQubitIndQubitBase, QOne]
      aesop
    simp
    rw [eq]
    clear eq
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl:
        (isoQubitIndQubitBase 1)
        (fun x:X2 => match x with | X2.a => 0 | X2.b => 1) = f
    have eq0: f 0 = 0 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    have eq1: f 1 = 1 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    simp [eq0, eq1]
  }
  {
    have eq: (QOneImage 2) = fun x:X3 => match x with | X3.a => 0 | X3.b => 1 := by
      simp [QOneImage, isoQubitIndQubitBase, QOne]
      aesop
    simp
    rw [eq]
    clear eq
    simp [IP.f]
    simp [IP.Transfer.lE]
    generalize repl:
        (isoQubitIndQubitBase 2)
        (fun x:X3 => match x with | X3.a => 0 | X3.b => 1) = f
    have eq0: f 0 = 0 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    have eq1: f 1 = 1 := by
      simp [Eq.symm repl, isoQubitIndQubitBase]
    simp [eq0, eq1]
  }
