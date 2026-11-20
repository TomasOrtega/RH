import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellParabolicUnipotentFactorization
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DCell.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBruhatCellParabolicUnipotentFactorization.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization : ∀ (n : ℕ) (y : PositivityTheory.Rg.Sw.GR n), ((PositivityTheory.Rg.Sw.mR y).toBlocks₂₂).det ≠ 0 → ∃ (p nbb : PositivityTheory.Rg.Sw.GR n) (c : Matrix (Fin n) (Fin n) ℂ), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ PositivityTheory.Rg.Sw.mR nbb = Matrix.fromBlocks 1 0 c 1 ∧ y = p * nbb := by
  first | exact @GlobalTheory.CompanionTheory.DCell.main | exact GlobalTheory.CompanionTheory.DCell.main | (intros; apply GlobalTheory.CompanionTheory.DCell.main <;> assumption)
