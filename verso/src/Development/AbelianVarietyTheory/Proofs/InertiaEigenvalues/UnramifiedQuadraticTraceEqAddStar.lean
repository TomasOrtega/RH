import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem trace_eq_add_star : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y := by
  intro F E _ _ _ _ hU y
  classical
  have hfr : Module.finrank F E = 2 := hU.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut E)) (fun x => hU.star_fix x)
  have hσ : ∀ z, σ z = star z := fun z => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro h
    obtain ⟨z, hz⟩ := hU.star_ne
    apply hz
    rw [← hσ, ← h]; rfl
  have hle : Nat.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hfr]
    exact (Nat.card_le_card_of_injective _ AlgEquiv.coe_algHom_injective).trans (card_algHom_le_finrank F E E)
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    refine le_antisymm hle ?_
    have : Fintype.card (E ≃ₐ[F] E) ≥ 2 := by
      have h2 : (({1, σ} : Finset (E ≃ₐ[F] E))).card = 2 := Finset.card_pair hne
      rw [← h2]; exact Finset.card_le_univ _
    rwa [Nat.card_eq_fintype_card]
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hfr])
  rw [trace_eq_sum_automorphisms]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} := by
    symm
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  rw [huniv, Finset.sum_pair hne]
  rfl

end GlobalTheory
