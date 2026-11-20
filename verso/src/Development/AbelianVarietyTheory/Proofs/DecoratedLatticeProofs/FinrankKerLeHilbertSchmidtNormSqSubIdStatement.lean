import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubId
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFinrankKerLeHilbertSchmidtNormSqSubId.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V), (∀ x ∈ N, K x = 0) → (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  first | exact @GlobalTheory.finrank_ker_le_hsNormSq_sub_id | exact GlobalTheory.finrank_ker_le_hsNormSq_sub_id | (intros; apply GlobalTheory.finrank_ker_le_hsNormSq_sub_id <;> assumption)
