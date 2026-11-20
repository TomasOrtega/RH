import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.mahler_mul_of_disjoint_support` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FMahlerJetCoefficientMulOfDisjointSupport.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι'] (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T → (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) → (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) → (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧ (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) * GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  first | exact @GlobalTheory.mahler_mul_of_disjoint_support | exact GlobalTheory.mahler_mul_of_disjoint_support | (intros; apply GlobalTheory.mahler_mul_of_disjoint_support <;> assumption)
