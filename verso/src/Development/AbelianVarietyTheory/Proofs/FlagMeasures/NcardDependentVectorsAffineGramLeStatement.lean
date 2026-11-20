import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardDependentVectorsAffineGramLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNcardDependentVectorsAffineGramLe.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.ncard_dependent_vectors_affine_gram_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B), Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by
  first | exact @GlobalTheory.GramCount.ncard_dependent_le | exact GlobalTheory.GramCount.ncard_dependent_le | (intros; apply GlobalTheory.GramCount.ncard_dependent_le <;> assumption)
