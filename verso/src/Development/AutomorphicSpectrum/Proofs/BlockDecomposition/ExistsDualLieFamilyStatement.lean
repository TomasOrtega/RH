import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamily
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RealCountG.dualFam_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsDualLieFamily.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_dual_lie_family : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | exact GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | (intros; apply GlobalTheory.CompanionTheory.RealCountG.dualFam_exists <;> assumption)
