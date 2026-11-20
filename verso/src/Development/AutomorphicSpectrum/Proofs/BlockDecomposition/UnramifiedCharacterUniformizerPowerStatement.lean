import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterUniformizerPower
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LFUDom.mp_uniformizerUnit_zpow_half` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedCharacterUniformizerPower.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.unramified_character_uniformizer_power : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (m t : ℤ), Ad3.mp (uniformizerUnit F ^ m) ((t : ℂ) / 2) = sqrtQ F ^ (-(t * m)) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.mp_uniformizerUnit_zpow_half | exact GlobalTheory.CompanionTheory.LFUDom.mp_uniformizerUnit_zpow_half | (intros; apply GlobalTheory.CompanionTheory.LFUDom.mp_uniformizerUnit_zpow_half <;> assumption)
