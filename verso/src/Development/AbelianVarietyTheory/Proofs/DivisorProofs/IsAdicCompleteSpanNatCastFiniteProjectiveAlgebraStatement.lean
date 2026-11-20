import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective | exact GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective <;> assumption)
