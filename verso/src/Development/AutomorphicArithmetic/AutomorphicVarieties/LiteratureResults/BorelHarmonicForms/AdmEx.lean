import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IsOpenUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Lit.Bor.admEx :
    UpperTheory.V.Lit.Bor.AdmEx := by
  intro E _ _ _ a Ξ
  obtain ⟨R, D, hRD, hD⟩ := cxExt E a Ξ
  obtain ⟨G, hG, hadj⟩ := admissible_abs_bound (E →+* ℂ) a Ξ.d R D hRD
  refine ⟨G, hG, fun X => ?_⟩
  have hs : (star X).map (emb E) = star (X.map (emb E)) := by
    ext i j τ
    exact UpperTheory.V.FieldIso.coord_star τ (X j i)
  rw [← hD, ← hD, hs]
  exact hadj _
