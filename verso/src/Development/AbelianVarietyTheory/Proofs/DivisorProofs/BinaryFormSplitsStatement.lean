import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinaryFormSplits
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBinaryFormSplits.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.exists_binary_form_eq_mul_prod_linear : ∀ (F : Type) [Field F] (m : ℕ) (p : Fin (m + 1) → F), p ≠ 0 → ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (c : E) (s t : Fin m → E), c ≠ 0 ∧ (∀ j, ![s j, t j] ≠ 0) ∧ ∀ (A : Type) [CommRing A] [Algebra E A] (x y : A), ∑ i : Fin (m + 1), algebraMap E A (algebraMap F E (p i)) * y ^ (i : ℕ) * x ^ (m - i) = algebraMap E A c * ∏ j, (algebraMap E A (s j) * x + algebraMap E A (t j) * y) := by
  first | exact @GlobalTheory.Nef.binary_form_splits | exact GlobalTheory.Nef.binary_form_splits | (intros; apply GlobalTheory.Nef.binary_form_splits <;> assumption)
