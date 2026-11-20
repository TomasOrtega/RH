import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLOfCompactInvertibleMatrices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsCompactGLOfCompactInvertibleMatrices.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isCompact_GL_of_compact_invertibleMatrices : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)), IsCompact T → T ⊆ invSet E n → IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  first | exact @GlobalTheory.WhitBump.isCompact_GL_of_invSet | exact GlobalTheory.WhitBump.isCompact_GL_of_invSet | (intros; apply GlobalTheory.WhitBump.isCompact_GL_of_invSet <;> assumption)
