import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerRatioValuationZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import GroundTheory.LocalFields.MainTheorem
import GroundTheory.GlobalFields.LocalFieldAtPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformizerRatioValuationZero.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.uniformizer_ratio_valuation_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) → GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | exact GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero <;> assumption)
