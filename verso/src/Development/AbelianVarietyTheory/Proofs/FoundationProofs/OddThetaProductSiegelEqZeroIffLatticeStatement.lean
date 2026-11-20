import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FOddThetaProductSiegelEqZeroIffLattice.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice : ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  first | exact @GlobalTheory.ThZero.th_eq_zero_iff | exact GlobalTheory.ThZero.th_eq_zero_iff | (intros; apply GlobalTheory.ThZero.th_eq_zero_iff <;> assumption)
