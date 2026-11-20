import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameEisensteinExtensionUniqueTotallyRamifiedPlac
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTameEisensteinExtensionUniqueTotallyRamifiedPlac.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (ϖ : 𝓞 E), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 →
    ∀ (π : Ω) [FiniteDimensional E (IntermediateField.adjoin E {π})] [NumberField (IntermediateField.adjoin E {π})],
    π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ W : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal ∧
      (∀ W' : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
        W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal → W' = W) ∧
      IsPlaceOver A W ∧ normV W = normV v ∧
      ∀ c : (W.adicCompletion (IntermediateField.adjoin E {π}))ˣ,
        (c : W.adicCompletion (IntermediateField.adjoin E {π})) =
          algebraMap (IntermediateField.adjoin E {π}) _ (IntermediateField.AdjoinSimple.gen E π) → IsUnifAt W c := by
  first | exact @GlobalTheory.TameRecPlace.main | exact GlobalTheory.TameRecPlace.main | (intros; apply GlobalTheory.TameRecPlace.main <;> assumption)
