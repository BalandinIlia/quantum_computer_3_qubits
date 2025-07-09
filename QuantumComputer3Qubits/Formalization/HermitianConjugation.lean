import QuantumComputer3Qubits.Formalization.OuterProduct
import QuantumComputer3Qubits.Formalization.OrthonormalBasis

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

-- This is a conjugate component.
noncomputable
def operCompConj{T: Type}
                [AddCommMonoid T]
                [Module ℂ T]
                [IP T]
                [ob: OrthonormalBasis T]
                (A: T →ₗ[ℂ] T)
                (i: Fin ob.N): T →ₗ[ℂ] T := 
                OP (ob.basis i) (A (ob.basis i))

-- This is a conjugate operator formulated as a sum of conjugate components.
noncomputable
def conj{T: Type}
        [AddCommMonoid T]
        [Module ℂ T]
        [IP T]
        [ob: OrthonormalBasis T]
        (A: T →ₗ[ℂ] T): T →ₗ[ℂ] T :=
        finsum (fun i: Fin ob.N => operCompConj A i)
