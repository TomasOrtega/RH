import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
import GroundTheory.LocalFields.Unramified
import GroundTheory.AutomorphicForms.Measures

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

/- English proof (translation)
Use `⟨fun F _ _ v n => rfl, fun F E _ _ _ _ _ v w hw n => ?_⟩` and prove the remaining obligations. Use extensionality with `g`. Use `⟨fun h => h w, fun h w' => ?_⟩` and prove the remaining obligations. Take `rfl` from `hw w'`. Conclude with `h`.
-/
theorem UpperTheory.V.Z.Tf.Orb.placeInt :
    UpperTheory.V.Z.Tf.Orb.PlaceInt := by
  refine ⟨fun F _ _ v n => rfl, fun F E _ _ _ _ _ v w hw n => ?_⟩
  ext g
  refine ⟨fun h => h w, fun h w' => ?_⟩
  obtain rfl := hw w'
  exact h
