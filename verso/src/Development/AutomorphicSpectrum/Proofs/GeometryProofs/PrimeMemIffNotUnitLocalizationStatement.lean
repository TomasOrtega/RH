import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalization
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FPrimeMemIffNotUnitLocalization.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.prime_mem_iff_not_unit_localization : ∀ {K : Type} [Field K] (T : Subring K) (P : Ideal T) (_ : P.IsPrime) (t : T), t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ (LocalSubring.ofPrime T P).toSubring) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem | exact GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem | (intros; apply GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem <;> assumption)
