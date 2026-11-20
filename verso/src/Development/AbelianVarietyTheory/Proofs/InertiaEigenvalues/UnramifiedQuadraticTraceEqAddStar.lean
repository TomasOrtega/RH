import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ hU y`. Establish `hfr : Module.finrank F E = 2` using `hU.finrank_eq`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Set `σ : E ≃ₐ[F] E` to `AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut E)) (fun x => hU.star_fix x)`. Establish `hσ : ∀ z, σ z = star z` using `fun z => rfl`.

Establish `hne : (1 : E ≃ₐ[F] E) ≠ σ`. Introduce `h`. Take `⟨z, hz⟩` from `hU.star_ne`. Apply `hz` to reduce the goal to its premises. Rewrite using `[← hσ, ← h]`.

Both sides reduce to the same expression. Establish `hle : Nat.card (E ≃ₐ[F] E) ≤ 2`. Rewrite using `[← hfr]`. Conclude with `(Nat.card_le_card_of_injective _ AlgEquiv.coe_algHom_injective).trans (card_algHom_le_finrank F E E)`. Establish `hcard : Fintype.card (E ≃ₐ[F] E) = 2`.

Rewrite using `[← Nat.card_eq_fintype_card]`. Use `le_antisymm hle ?_` and prove the remaining obligations. Establish `: Fintype.card (E ≃ₐ[F] E) ≥ 2`. Establish `h2 : (({1, σ} : Finset (E ≃ₐ[F] E))).card = 2` using `Finset.card_pair hne`. Rewrite using `[← h2]`.

Conclude with `Finset.card_le_univ _`. Rewrite using `[Nat.card_eq_fintype_card]` and apply the resulting hypothesis. Use `haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hfr])`. Rewrite using `[trace_eq_sum_automorphisms]`. Establish `huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ}`.

Use `symm`. Use `Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_` and prove the remaining obligations. Rewrite using `[Finset.card_univ, hcard, Finset.card_pair hne]`. Rewrite using `[huniv, Finset.sum_pair hne]`. Both sides reduce to the same expression.
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
