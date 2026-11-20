import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleEqNormModule
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleConjugationInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBaseChangeSqStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIdeleModuleEqNormModule.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.idele_module_eq_norm_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ x n → (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm <;> assumption)
