import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ H hH hc μ hμ`. Use `haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _`. Use `letI : CommGroup H := { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }`. Use `⟨inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular μ, ⟨fun g => ?_⟩⟩` and prove the remaining obligations.

Establish `: (fun h : H => h * g) = fun h => g * h` using `funext fun h => mul_comm h g`. Rewrite using `[this]`. Conclude with `map_mul_left_eq_self μ g`.
-/
theorem UpperTheory.V.Z.Tf.Orb.haarComm :
    UpperTheory.V.Z.Tf.Orb.HaarComm := by
  intro G _ _ _ _ _ _ _ _ H hH hc μ hμ
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  refine ⟨inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular μ, ⟨fun g => ?_⟩⟩
  have : (fun h : H => h * g) = fun h => g * h := funext fun h => mul_comm h g
  rw [this]
  exact map_mul_left_eq_self μ g
