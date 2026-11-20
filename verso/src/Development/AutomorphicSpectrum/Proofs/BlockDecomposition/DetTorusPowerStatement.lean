import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetTorusPower
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDetTorusPower.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.det_torus_power : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℤ), GeneralLinearGroup.det (torusPow F n l) = uniformizerUnit F ^ (∑ i, l i) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.det_torusPow_eq | exact GlobalTheory.CompanionTheory.LFUDom.det_torusPow_eq | (intros; apply GlobalTheory.CompanionTheory.LFUDom.det_torusPow_eq <;> assumption)
