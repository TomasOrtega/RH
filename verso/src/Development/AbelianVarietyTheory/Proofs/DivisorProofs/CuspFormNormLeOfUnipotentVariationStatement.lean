import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariation
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCuspFormNormLeOfUnipotentVariation.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ), (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  first | exact @GlobalTheory.CuspRep.norm_le_of_unip_variation | exact GlobalTheory.CuspRep.norm_le_of_unip_variation | (intros; apply GlobalTheory.CuspRep.norm_le_of_unip_variation <;> assumption)
