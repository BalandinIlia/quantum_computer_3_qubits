import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis
import QuantumComputer3Qubits.Formalization.FiniteSum

-- HC means "Hermitian Conjugation"
namespace HC

-- This is kind of operator component associated with the i-th
-- vector of orthonormal basis.
-- Sum of all components is equal to the operator.
noncomputable
def operComp{T: Type}
            [AddCommMonoid T]
            [Module ℂ T]
            [IP T]
            [ob: OrthonormalBasis T]
            (A: T →ₗ[ℂ] T)
            (i: Fin ob.N): T →ₗ[ℂ] T :=
            OP (A (ob.basis i)) (ob.basis i)

lemma reprOp{T: Type}
            [AddCommMonoid T]
            [Module ℂ T]
            [IP T]
            [ob: OrthonormalBasis T]
            (pos: ob.N > 0)
            (A: T →ₗ[ℂ] T):
A = FS.fs (fun i: Fin ob.N => operComp A i) := by
       ext s
       have rt := FS.basisReprAx ob.N (by aesop) ob.basis s
       simp [FS.basisRepr] at rt
       rw [FS.applyMap]
       rw [rt]
       rw [FS.applyDistr]
       simp [FS.applyDistr]
       simp [operComp, OP]
       simp [ob.prop]
       let st := @FS.doubleFS T _ ob.N pos (fun i: Fin ob.N => fun i_1: Fin ob.N => (OrthonormalBasis.basis.repr s) i • A (OrthonormalBasis.basis i_1))
       simp [st]

-- This is an adjoint component.
noncomputable
def operCompAdj{T: Type}
               [AddCommMonoid T]
               [Module ℂ T]
               [IP T]
               [ob: OrthonormalBasis T]
               (A: T →ₗ[ℂ] T)
               (i: Fin ob.N): T →ₗ[ℂ] T :=
               OP (ob.basis i) (A (ob.basis i))

-- This is an adjoint operator formulated as a sum of adjoint components.
noncomputable
def adj{T: Type}
       [AddCommMonoid T]
       [Module ℂ T]
       [IP T]
       [ob: OrthonormalBasis T]
       (A: T →ₗ[ℂ] T): T →ₗ[ℂ] T :=
       FS.fs (fun i: Fin ob.N => operCompAdj A i)
