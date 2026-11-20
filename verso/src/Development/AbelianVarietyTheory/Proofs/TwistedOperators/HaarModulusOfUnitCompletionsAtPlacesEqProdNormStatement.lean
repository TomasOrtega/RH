import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNorm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ModuPiLocal.modu_sPart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHaarModulusOfUnitCompletionsAtPlacesEqProdNorm.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.haarModulusOfUnit_completionsAtPlaces_eq_prod_norm : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SPart F S), IsUnit x → (modu (SPart F S) x : ℝ) = ∏ v : S, ‖x v‖ := by
  first | exact @GlobalTheory.ModuPiLocal.modu_sPart | exact GlobalTheory.ModuPiLocal.modu_sPart | (intros; apply GlobalTheory.ModuPiLocal.modu_sPart <;> assumption)
