import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBoundedOnCompact
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIdeleModuleBoundedOnCompact.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.idele_module_bounded_on_compact : ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdeleRing (𝓞 K) K)), IsCompact C → ∃ R : ℝ, ∀ a : IdeleGroup K, (a : AdeleRing (𝓞 K) K) ∈ C → (IdeleGroup.ideleModule K a : ℝ) ≤ R := by
  first | exact @GlobalTheory.CompanionTheory.IdeleModBdd.ideleModule_bounded_on_compact | exact GlobalTheory.CompanionTheory.IdeleModBdd.ideleModule_bounded_on_compact | (intros; apply GlobalTheory.CompanionTheory.IdeleModBdd.ideleModule_bounded_on_compact <;> assumption)
