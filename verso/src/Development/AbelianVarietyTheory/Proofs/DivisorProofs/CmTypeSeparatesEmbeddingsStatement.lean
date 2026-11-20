import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddings
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMSep.exists_int_ne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCmTypeSeparatesEmbeddings.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.cm_type_separates_embeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i k, i ≠ k → ∃ a : 𝓞 (FR E), φ i ((a : FR E) : E) ≠ φ k ((a : FR E) : E) := by
  first | exact @GlobalTheory.CMSep.exists_int_ne | exact GlobalTheory.CMSep.exists_int_ne | (intros; apply GlobalTheory.CMSep.exists_int_ne <;> assumption)
