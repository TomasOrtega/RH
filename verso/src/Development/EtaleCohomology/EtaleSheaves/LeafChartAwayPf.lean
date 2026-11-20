import Development.EtaleCohomology.EtaleSheaves.LeafChartPf

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LeafChartAwayPf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem LeafChartAway_of : LateralTheory.E.LeafChartPf.LeafChartAway := by
  intro X Y B _ j _ I g hj
  let f := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  have hf : ∀ y : Spec (CommRingCat.of (Localization.Away g)),
      f y = PrimeSpectrum.comap (algebraMap B (Localization.Away g)) y := fun _ => rfl
  refine ⟨f ≫ j, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨y', rfl⟩
    exact ⟨f y', rfl⟩
  · intro y hy
    have hmem : (show PrimeSpectrum B from y) ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hy
    obtain ⟨y', hy'⟩ := hmem
    refine ⟨y', ?_⟩
    show j (f y') = j y
    exact congrArg j ((hf y').trans hy')
  · intro y'
    change j (f y') ∈ Y ↔ _
    rw [hj, hf, Ideal.map_le_iff_le_comap]
    rfl

end LateralTheory.E.LeafChartAwayPf
