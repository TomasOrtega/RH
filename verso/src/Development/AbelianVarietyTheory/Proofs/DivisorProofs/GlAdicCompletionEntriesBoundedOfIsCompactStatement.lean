import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlAdicCompletionEntriesBoundedOfIsCompact
import Mathlib
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGlAdicCompletionEntriesBoundedOfIsCompact.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.gl_adicCompletion_entries_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))), IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j, Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
  first | exact @GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact | exact GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact | (intros; apply GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact <;> assumption)
