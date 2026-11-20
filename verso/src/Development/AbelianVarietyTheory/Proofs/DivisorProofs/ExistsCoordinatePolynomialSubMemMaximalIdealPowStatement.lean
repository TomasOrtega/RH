import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatePolynomialSubMemMaximalIdealPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCoordinatePolynomialSubMemMaximalIdealPow.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (z : Fin n → A), maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ (k : ℕ) (f : A), ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | exact GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | (intros; apply GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow <;> assumption)
