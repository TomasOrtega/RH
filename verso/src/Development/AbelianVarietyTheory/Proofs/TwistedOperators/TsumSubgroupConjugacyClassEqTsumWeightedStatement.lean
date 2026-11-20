import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSubgroupConjugacyClassEqTsumWeighted
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FTsumSubgroupConjugacyClassEqTsumWeighted.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.tsum_subgroupConjugacyClass_eq_tsum_weighted : ∀ (H : Type) [Group H] (Γ : Subgroup H) (γ : H), γ ∈ Γ → ∀ (α : H → ℝ≥0∞), (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) → ∀ (G : H → ℝ≥0∞) (x : H), ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) = ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) := by
  first | exact @GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted | exact GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted | (intros; apply GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted <;> assumption)
