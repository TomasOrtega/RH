import Mathlib
open IsLocalRing

namespace GlobalTheory.EtaleDescent

open TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem exists_etale_model_of_directed_union :
    ∀ (R : Type) [CommRing R] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (Ri : ι → Subring R), Monotone Ri → (∀ x, ∃ i, x ∈ Ri i) →
      ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A],
        ∃ (i : ι) (Ai : Type) (_ : CommRing Ai) (_ : Algebra (Ri i) Ai),
          Algebra.Etale (Ri i) Ai ∧ Nonempty (TensorProduct (Ri i) R Ai ≃ₐ[R] A) := by
  intro R _ ι _ _ _ Ri hmono hcov A _ _ _
  obtain ⟨κ, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := A)).mp
      inferInstance |>.out

  have hfin := P.finite_coeffs
  have hex : ∃ i, P.coeffs ⊆ (Ri i : Set R) := by
    classical
    choose j hj using hcov
    obtain ⟨i, hi⟩ := Finset.exists_le (hfin.toFinset.image j)
    refine ⟨i, fun x hx ↦ hmono (hi _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx))) (hj x)⟩
  obtain ⟨i, hi⟩ := hex
  letI : Algebra (Ri i) A := ((algebraMap R A).comp (algebraMap (Ri i) R)).toAlgebra
  haveI : IsScalarTower (Ri i) R A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (Ri i) := ⟨fun x hx ↦ ⟨⟨x, hi hx⟩, rfl⟩⟩
  let Q := P.ofHasCoeffs (Ri i)
  refine ⟨i, P.ModelOfHasCoeffs (Ri i), inferInstance, inferInstance, ?_,
    ⟨P.tensorModelOfHasCoeffsEquiv (Ri i)⟩⟩
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (Ri i) (P.ModelOfHasCoeffs (Ri i)) :=
    Q.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  infer_instance

end GlobalTheory.EtaleDescent
