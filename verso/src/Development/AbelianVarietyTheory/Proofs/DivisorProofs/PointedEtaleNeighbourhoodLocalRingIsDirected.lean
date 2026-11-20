import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation

open scoped TensorProduct

namespace GlobalTheory.Henselisation

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem etNbhd_isDirected (R : Type) [CommRing R] [IsLocalRing R] :
    IsDirected (EtNbhd R) (· ≤ ·) := by
  refine ⟨fun i j => ?_⟩
  let C := i.A ⊗[R] j.A
  haveI : Algebra.Etale R C := Algebra.Etale.comp R i.A C
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := C)).1 inferInstance
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let P : C →ₐ[R] ResidueField R := Algebra.TensorProduct.lift i.pt j.pt (fun _ _ => Commute.all _ _)
  let k : EtNbhd R :=
    { n := n, I := RingHom.ker f, etale := Algebra.Etale.of_equiv e.symm, pt := P.comp e.toAlgHom }
  refine ⟨k, ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeLeft, ?_⟩,
    ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeRight, ?_⟩⟩
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = i.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P (a ⊗ₜ[R] (1 : j.A)) = i.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = j.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P ((1 : i.A) ⊗ₜ[R] a) = j.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end GlobalTheory.Henselisation
