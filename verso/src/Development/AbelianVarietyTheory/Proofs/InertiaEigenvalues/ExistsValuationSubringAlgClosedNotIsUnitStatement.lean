import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationSubringAlgClosedNotIsUnit
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsValuationSubringAlgClosedNotIsUnit.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit : ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u → ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V), ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  first | exact @GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | exact GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | (intros; apply GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero <;> assumption)
