import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeviEmbeddingHeightBound.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.levi_embedding_height_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | exact GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le <;> assumption)
