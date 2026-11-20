import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
-/
theorem GlobalTheory.QNorm.exists_ringHom_adicCompletion_under :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (w : HeightOneSpectrum (𝓞 E)),
      ∃ φ : (w.under (𝓞 F)).adicCompletion F →+* w.adicCompletion E,
        ∀ x : F, φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
          algebraMap E (w.adicCompletion E) (algebraMap F E x) := by
  intro K L _ _ _ _ _ w
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K))
    w).continuous
  refine ⟨((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((w.under (𝓞 K)).valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K (w.under (𝓞 K))).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
