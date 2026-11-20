import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UnrDens.solCount_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCardUnimodularHermitianRepsLevelOne.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.card_unimodular_hermitian_reps_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → (solCount σ ϖ S T 1 : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.solCount_one | exact GlobalTheory.CompanionTheory.UnrDens.solCount_one | (intros; apply GlobalTheory.CompanionTheory.UnrDens.solCount_one <;> assumption)
