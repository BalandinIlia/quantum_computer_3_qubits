import QuantumComputer3Qubits.Formalization.InnerProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.HermitianConjugation
import QuantumComputer3Qubits.Formalization.FiniteSum

namespace Test_HermitianConjugation
open HC

theorem test1{T: Type}
             [AddCommMonoid T]
             [Module ℂ T]
             [IP T]
             [ob: OrthonormalBasis T]
             (A: T →ₗ[ℂ] T):
∀i: Fin ob.N, isAdj (operCompAdj A i) (operComp A i) := by
  intro i
  simp [isAdj, operComp, operCompAdj, OP]
  intro x y
  simp [IP.smulLeft, IP.smulRight]
  simp [IP.comm x]
  generalize r₁: (IP.f (OrthonormalBasis.basis i) x) = c₁
  generalize r₂: IP.f (A (OrthonormalBasis.basis i)) y = c₂
  clear r₁ r₂
  clear A i x y
  ring
