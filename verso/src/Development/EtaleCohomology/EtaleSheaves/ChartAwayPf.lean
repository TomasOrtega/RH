import Development.EtaleCohomology.EtaleSheaves.LeafChartAffPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.ChartAwayPf

/- English proof (translation)
Introduce `X Y B _ j _ I g hj`. Set `f` to `Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))`. Establish `hf : ∀ y' : Spec (CommRingCat.of (Localization.Away g)), (show PrimeSpectrum B from f.base y') = PrimeSpectrum.comap (algebraMap B (Localization.Away g)) (show PrimeSpectrum _ from y')` using `fun _ => rfl`. Use `⟨f ≫ j, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `⟨f.base y, rfl⟩`. Introduce `y hy`. Establish `: (show PrimeSpectrum B from y) ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g)))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]`. Conclude with `hy`.

Take `⟨y', hy'⟩` from `this`. Use `⟨y', ?_⟩` and prove the remaining obligations. Use `show j.base (f.base y') = j.base y`. Rewrite using `[show f.base y' = y from (hf y').trans hy']`. Introduce `y' show j.base (f.base y') ∈ Y ↔ _`.

Rewrite using `[hj (f.base y'), hf y', Ideal.map_le_iff_le_comap]`. Both sides reduce to the same expression.
-/
theorem ChartAway_of : LateralTheory.E.LeafChartAffPf.ChartAway := by
  intro X Y B _ j _ I g hj
  let f := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  have hf : ∀ y' : Spec (CommRingCat.of (Localization.Away g)),
      (show PrimeSpectrum B from f.base y') =
        PrimeSpectrum.comap (algebraMap B (Localization.Away g)) (show PrimeSpectrum _ from y') := fun _ => rfl
  refine ⟨f ≫ j, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨f.base y, rfl⟩
  · intro y hy
    have : (show PrimeSpectrum B from y) ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hy
    obtain ⟨y', hy'⟩ := this
    refine ⟨y', ?_⟩
    show j.base (f.base y') = j.base y
    rw [show f.base y' = y from (hf y').trans hy']
  · intro y'
    show j.base (f.base y') ∈ Y ↔ _
    rw [hj (f.base y'), hf y', Ideal.map_le_iff_le_comap]
    rfl

end LateralTheory.E.ChartAwayPf
