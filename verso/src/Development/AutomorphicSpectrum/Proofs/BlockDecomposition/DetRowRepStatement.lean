import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetRowRep
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDetRowRep.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.det_row_rep : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (i j : ℕ) (c : Fin j → 𝓀[F]), GeneralLinearGroup.det (rowRep i j c) = uniformizerUnit F ^ ((i : ℤ) + j) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.det_rowRep_eq_zpow | exact GlobalTheory.CompanionTheory.LFUDom.det_rowRep_eq_zpow | (intros; apply GlobalTheory.CompanionTheory.LFUDom.det_rowRep_eq_zpow <;> assumption)
