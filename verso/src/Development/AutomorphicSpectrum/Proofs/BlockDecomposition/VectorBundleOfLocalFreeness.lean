import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Cot

/- English proof (translation)
Introduce `R W _ _ _ g h`. Use `choose r hr hfree hfin hrank using h`. Establish `hs : Ideal.span (Set.range r) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Conclude with `hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))`. Establish `hfp : Module.FinitePresentation R W`. Use `Module.FinitePresentation.of_localizationSpan' (Set.range r) hs (Rₚ := fun x => Localization.Away x.1) (Mₚ := fun x => Localization.Away x.1 ⊗[R] W) (fun x => TensorProduct.mk R (Localization.Away x.1) W 1) (fun x => ?_)` and prove the remaining obligations. Take `⟨x, p, rfl⟩` from `x`. Use `hfree p` as an intermediate fact.

Use `hfin p` as an intermediate fact. Conclude with `Module.finitePresentation_of_projective (Localization.Away (r p)) (Localization.Away (r p) ⊗[R] W)`. Establish `hproj : Module.Projective R W`. Rewrite using `[← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]`. Introduce `p`.

Establish `hsub : (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R W`. Rewrite using `[Module.basicOpen_subset_freeLocus_iff]`. Use `hfree p` as an intermediate fact. Conclude with `Module.Projective.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers (r p)) W).symm`. Conclude with `hsub (hr p)`.

Use `⟨inferInstance, hproj, fun p => ?_⟩` and prove the remaining obligations. Establish `hfl` using `hfree p`. Establish `hfi` using `hfin p`. Establish `hrange` using `PrimeSpectrum.localization_away_comap_range (Localization.Away (r p)) (r p)`. Establish `hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r p))))`.

Rewrite using `[hrange]`. Conclude with `hr p`. Take `⟨q', hq'⟩` from `hp`. Rewrite using `[← hq', ← Module.rankAtStalk_baseChange q', Module.rankAtStalk_eq_finrank_of_free]`. Conclude with `hrank p`.
-/
theorem vb_of_free_on_basicOpens :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ),
      (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
        Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by
  intro R W _ _ _ g h
  choose r hr hfree hfin hrank using h
  have hs : Ideal.span (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have hfp : Module.FinitePresentation R W := by
    refine Module.FinitePresentation.of_localizationSpan' (Set.range r) hs
      (Rₚ := fun x => Localization.Away x.1) (Mₚ := fun x => Localization.Away x.1 ⊗[R] W)
      (fun x => TensorProduct.mk R (Localization.Away x.1) W 1) (fun x => ?_)
    obtain ⟨x, p, rfl⟩ := x
    have := hfree p
    have := hfin p
    exact Module.finitePresentation_of_projective (Localization.Away (r p))
      (Localization.Away (r p) ⊗[R] W)
  have hproj : Module.Projective R W := by
    rw [← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
    intro p
    have hsub : (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R W := by
      rw [Module.basicOpen_subset_freeLocus_iff]
      have := hfree p
      exact Module.Projective.of_equiv
        (LocalizedModule.equivTensorProduct (Submonoid.powers (r p)) W).symm
    exact hsub (hr p)
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hfl := hfree p
  have hfi := hfin p
  have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (r p)) (r p)
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r p)))) := by
    rw [hrange]
    exact hr p
  obtain ⟨q', hq'⟩ := hp
  rw [← hq', ← Module.rankAtStalk_baseChange q', Module.rankAtStalk_eq_finrank_of_free]
  exact hrank p

end GlobalTheory.CompanionTheory.Cot
