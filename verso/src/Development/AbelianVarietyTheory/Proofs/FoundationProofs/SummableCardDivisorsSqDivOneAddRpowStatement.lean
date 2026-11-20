import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpow
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSummableCardDivisorsSqDivOneAddRpow.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.summable_card_divisors_sq_div_one_add_rpow : ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ (1 + s) := by
  first | exact @GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow | exact GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow | (intros; apply GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow <;> assumption)
