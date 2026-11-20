import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSumNormSqOrthonormalLeHilbertSchmidt.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt : ∀ {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (A : V →L[ℂ] H) {ι : Type} [Fintype ι] (v : ι → V), Orthonormal ℂ v → ∑ i, ‖A (v i)‖ ^ 2 ≤ hsNormSq A := by
  first | exact @GlobalTheory.sum_norm_sq_le_hsNormSq | exact GlobalTheory.sum_norm_sq_le_hsNormSq | (intros; apply GlobalTheory.sum_norm_sq_le_hsNormSq <;> assumption)
