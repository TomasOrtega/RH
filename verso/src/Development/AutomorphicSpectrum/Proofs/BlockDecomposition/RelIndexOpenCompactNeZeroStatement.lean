import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZero
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRelIndexOpenCompactNeZero.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.relIndex_open_compact_ne_zero : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen <;> assumption)
