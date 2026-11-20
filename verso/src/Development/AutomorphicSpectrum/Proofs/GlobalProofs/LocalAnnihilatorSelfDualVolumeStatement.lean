import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAnnihilatorSelfDualVolume
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FLocalAnnihilatorSelfDualVolume.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.adelic_character_trivial_almost_everywhere : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) → (∀ v ∈ T, c v = 0) → psiF ψ c = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish <;> assumption)
