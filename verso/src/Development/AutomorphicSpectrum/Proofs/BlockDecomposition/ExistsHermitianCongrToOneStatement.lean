import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHermitianCongrToOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UnrDens.exists_congr_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsHermitianCongrToOne.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_hermitian_congr_to_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det → ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | exact GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_congr_one <;> assumption)
