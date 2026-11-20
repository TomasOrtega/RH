import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductEqOddThetaProductQuotient
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Sieg.ThQuot.cth_eq_th_quot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSmoothedThetaQProductEqOddThetaProductQuotient.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → th ((c : ℂ) * z) τ ≠ 0 → cth c (ee (τ : ℂ)) (ee z) = (-1) ^ (c * (c - 1) / 2) * th z τ ^ (c ^ 2) / th ((c : ℂ) * z) τ := by
  first | exact @GlobalTheory.Sieg.ThQuot.cth_eq_th_quot | exact GlobalTheory.Sieg.ThQuot.cth_eq_th_quot | (intros; apply GlobalTheory.Sieg.ThQuot.cth_eq_th_quot <;> assumption)
