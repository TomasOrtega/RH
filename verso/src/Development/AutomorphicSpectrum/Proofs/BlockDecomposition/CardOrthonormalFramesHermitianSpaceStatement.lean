import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCardOrthonormalFramesHermitianSpace.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.card_orthonormal_frames_hermitian_space : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | exact GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples <;> assumption)
