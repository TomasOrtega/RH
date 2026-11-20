import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct

namespace GlobalTheory

namespace PDiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cotMap_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A]
    [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A),
    (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 →
      b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) →
    Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  intro R C A _ _ _ _ _ f h
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨c, rfl⟩ := AugCot.d_surjective _ w
  have hw' : dUnit R (f c) = 0 := (cotMap_d f c).symm.trans hw
  rw [dUnit, AugCot.d_eq_zero_iff] at hw'
  change AugCot.d _ c = 0
  rw [AugCot.d_eq_zero_iff]
  apply h
  have e : Bialgebra.counitAlgHom R A (f c) = Bialgebra.counitAlgHom R C c :=
    AlgHom.congr_fun (BialgHomClass.counitAlgHom_comp f) c
  have e2 : f (c - algebraMap R C (Bialgebra.counitAlgHom R C c)) =
      f c - algebraMap R A (Bialgebra.counitAlgHom R A (f c)) := by
    rw [map_sub, e]
    congr 1
    exact AlgHom.commutes (f : C →ₐ[R] A) _
  rw [e2]
  exact hw'

end PDiv

end GlobalTheory
