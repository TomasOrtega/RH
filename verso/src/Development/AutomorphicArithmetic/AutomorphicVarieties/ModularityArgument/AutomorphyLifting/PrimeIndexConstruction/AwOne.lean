import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBad
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppSmo
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeEigenvalueBasicProperties

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ _ l _ n hn ι r π hπ hwin π' _ hπ'`. Take `⟨t, ht⟩` from `hwin`. Use `⟨t, fun v => UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo F n hn π π' ?_ t v (ht v)⟩` and prove the remaining obligations. Use `filter_upwards [hπ.2, hπ'.2] with w h1 h2`. Take `⟨B, hB, hE⟩` from `h1`.

Take `⟨B', hB', hE'⟩` from `h2`. Establish `e : B = B'` using `(UpperTheory.hecke_eigenvalue_basic_properties F Ω l ι w).2.2 n r B B' hE hE'`. Conclude with `⟨B, hB, e ▸ hB'⟩`.
-/
theorem UpperTheory.V.Z.Win.Birth.awOne :
    UpperTheory.V.Z.Win.Birth.AwOne := by
  intro F Ω _ _ _ _ _ _ l _ n hn ι r π hπ hwin π' _ hπ'
  obtain ⟨t, ht⟩ := hwin
  refine ⟨t, fun v => UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo F n hn π π' ?_ t v (ht v)⟩
  filter_upwards [hπ.2, hπ'.2] with w h1 h2
  obtain ⟨B, hB, hE⟩ := h1
  obtain ⟨B', hB', hE'⟩ := h2
  have e : B = B' := (UpperTheory.hecke_eigenvalue_basic_properties F Ω l ι w).2.2 n r B B' hE hE'
  exact ⟨B, hB, e ▸ hB'⟩
