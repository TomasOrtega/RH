import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHom
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothRangeOfIdempotentAlgHom.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.smooth_range_of_idempotent_algHom : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  first | exact @GlobalTheory.smooth_range_of_idempotent | exact GlobalTheory.smooth_range_of_idempotent | (intros; apply GlobalTheory.smooth_range_of_idempotent <;> assumption)
