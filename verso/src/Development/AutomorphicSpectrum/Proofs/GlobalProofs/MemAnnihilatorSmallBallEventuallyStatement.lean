import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventually
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FMemAnnihilatorSmallBallEventually.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.adelic_annihilator_box_product : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA <;> assumption)
