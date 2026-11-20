import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal

open scoped IntermediateField.algebraAdjoinAdjoin in

/- English proof (translation)
Introduce `K κ _ _ inst k R π hfrac ⟨z, hz⟩`. Establish `hiff : ∀ u : Fin k → κ, TrBasis (algebraMap ℂ κ) u ↔ IsTranscendenceBasis ℂ u`. Introduce `u`. Establish `: (algebraMap ℂ κ).toAlgebra = inst` using `Algebra.algebra_ext _ _ fun _ => rfl`. Unfold `TrBasis`.

Rewrite using `[this]`. Establish `hz'` using `(hiff z).1 hz`. Establish `htop : IntermediateField.adjoin ℂ (Set.range π) = ⊤`. Use `eq_top_iff.2 fun f _ => ?_` and prove the remaining obligations. Take `⟨a, b, hb, e⟩` from `hfrac f`.

Establish `: f = π a / π b` using `by rw [← e, mul_div_cancel_right₀ _ hb]`. Rewrite using `[this]`. Conclude with `div_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩)`. Establish `halg : Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range π)) κ` using `⟨fun f => isAlgebraic_algebraMap (⟨f, htop ▸ IntermediateField.mem_top⟩ : IntermediateField.adjoin ℂ (Set.range π))⟩`. Establish `halg' : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range π)) κ` using `IntermediateField.isAlgebraic_adjoin_iff_top.mp halg`.

Take `⟨t, ht, hb⟩` from `exists_isTranscendenceBasis_subset (R := ℂ) (Set.range π)`. Establish `hc : Cardinal.mk (Fin k) = Cardinal.mk t`. Rewrite using `[hb.cardinalMk_eq_trdeg, hz'.cardinalMk_eq_trdeg]`. Take `⟨e⟩` from `Cardinal.eq.mp hc`. Use `choose J hJ using fun i : Fin k => ht (e i).2`.

Use `⟨J, (hiff _).2 ?_⟩` and prove the remaining obligations. Use `(isTranscendenceBasis_equiv e).2 hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `hJ i`.
-/
theorem exists_trBasis_lift : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ κ] (k : ℕ) (R : Subring K) (π : R →+* κ),
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  ∃ zR : Fin k → R, TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) := by
  intro K κ _ _ inst k R π hfrac ⟨z, hz⟩
  have hiff : ∀ u : Fin k → κ, TrBasis (algebraMap ℂ κ) u ↔ IsTranscendenceBasis ℂ u := by
    intro u
    have : (algebraMap ℂ κ).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [this]
  have hz' := (hiff z).1 hz
  have htop : IntermediateField.adjoin ℂ (Set.range π) = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨a, b, hb, e⟩ := hfrac f
    have : f = π a / π b := by rw [← e, mul_div_cancel_right₀ _ hb]
    rw [this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range π)) κ :=
    ⟨fun f => isAlgebraic_algebraMap
      (⟨f, htop ▸ IntermediateField.mem_top⟩ : IntermediateField.adjoin ℂ (Set.range π))⟩
  have halg' : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range π)) κ :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp halg
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range π)
  have hc : Cardinal.mk (Fin k) = Cardinal.mk t := by
    rw [hb.cardinalMk_eq_trdeg, hz'.cardinalMk_eq_trdeg]
  obtain ⟨e⟩ := Cardinal.eq.mp hc
  choose J hJ using fun i : Fin k => ht (e i).2
  refine ⟨J, (hiff _).2 ?_⟩
  have := (isTranscendenceBasis_equiv e).2 hb
  convert this using 1
  funext i
  exact hJ i

end GlobalTheory.GraphLocal
