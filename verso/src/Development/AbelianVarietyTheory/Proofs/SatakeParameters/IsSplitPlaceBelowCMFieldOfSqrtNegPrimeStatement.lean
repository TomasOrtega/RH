import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceBelowCMFieldOfSqrtNegPrime
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationComplexConjOfNotSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIsSplitPlaceBelowCMFieldOfSqrtNegPrime.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.isSplitPlaceBelowCMField_of_sqrt_neg_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  first | exact @GlobalTheory.SplitOfNegPrime.isSplitAt | exact GlobalTheory.SplitOfNegPrime.isSplitAt | (intros; apply GlobalTheory.SplitOfNegPrime.isSplitAt <;> assumption)
