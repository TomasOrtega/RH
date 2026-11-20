import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTotallyComplexOfPrimitiveRootThreeLe
import Mathlib
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsTotallyComplexOfPrimitiveRootThreeLe.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.isTotallyComplex_of_primitiveRoot_three_le : ∀ (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ), IsPrimitiveRoot ζ m → 3 ≤ m →
    NumberField.IsTotallyComplex K := by
  first | exact @GlobalTheory.tcroot | exact GlobalTheory.tcroot | (intros; apply GlobalTheory.tcroot <;> assumption)
