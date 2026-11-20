import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicIntegralDenominator
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCompactAdelicIntegralDenominator.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.compact_adelic_integral_denominator : ∀ (E : Type) [Field E] [NumberField E] (Q : Set (Af E)), IsCompact Q →
    ∃ D : ℕ, D ≠ 0 ∧ ∀ x : E, algebraMap E (Af E) x ∈ Q → ∃ r : 𝓞 E, (r : E) = D * x := by
  first | exact @GlobalTheory.CompanionTheory.AdeleDen.exists_common_denominator | exact GlobalTheory.CompanionTheory.AdeleDen.exists_common_denominator | (intros; apply GlobalTheory.CompanionTheory.AdeleDen.exists_common_denominator <;> assumption)
