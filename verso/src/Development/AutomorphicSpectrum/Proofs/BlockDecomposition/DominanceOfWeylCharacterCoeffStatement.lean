import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominanceOfWeylCharacterCoeff
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDominanceOfWeylCharacterCoeff.lean&line=270#L270)
-/
theorem _root_.GlobalTheory.T.dominance_of_weyl_character_coeff : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ p : LP n, p * altL (delZ n) ^ 2 = pPL n * altL (lam + delZ n) ^ 2 →
    ∀ μ, p.coeff μ ≠ 0 → DomLE (wtR μ) (m0 lam) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.DomA.domLE_of_mul_eq | exact GlobalTheory.CompanionTheory.RealCountG.DomA.domLE_of_mul_eq | (intros; apply GlobalTheory.CompanionTheory.RealCountG.DomA.domLE_of_mul_eq <;> assumption)
