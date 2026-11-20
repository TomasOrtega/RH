import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquare
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitFlip.mem_innerVertices_flipPath` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMemGridPathInnerVerticesFlipGridPathAtSquare.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  first | exact @GlobalTheory.SplitFlip.mem_innerVertices_flipPath | exact GlobalTheory.SplitFlip.mem_innerVertices_flipPath | (intros; apply GlobalTheory.SplitFlip.mem_innerVertices_flipPath <;> assumption)
