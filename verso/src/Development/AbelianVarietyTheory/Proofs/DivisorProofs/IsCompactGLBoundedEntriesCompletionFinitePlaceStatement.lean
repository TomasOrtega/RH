import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlace
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BoundedGL.isCompact_bounded` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsCompactGLBoundedEntriesCompletionFinitePlace.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧ Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  first | exact @GlobalTheory.BoundedGL.isCompact_bounded | exact GlobalTheory.BoundedGL.isCompact_bounded | (intros; apply GlobalTheory.BoundedGL.isCompact_bounded <;> assumption)
