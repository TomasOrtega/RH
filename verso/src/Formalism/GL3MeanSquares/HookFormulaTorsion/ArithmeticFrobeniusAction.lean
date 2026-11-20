import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

/- English proof (translation)
Rewrite using `[← map_pow]`. Use extensionality with `n`. Rewrite using `[WittVector.coeff_frobenius_charP]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite using `[WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]`.

Rewrite using `[WittVector.teichmuller_coeff_pos p _ n hn, WittVector.teichmuller_coeff_pos p _ n hn, zero_pow (Fact.out : p.Prime).ne_zero]`.
-/
private theorem frob_teich (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p] (x : k) :
    WittVector.frobenius (WittVector.teichmuller p x) = (WittVector.teichmuller p x) ^ p := by
  rw [← map_pow]
  ext n
  rw [WittVector.coeff_frobenius_charP]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  · rw [WittVector.teichmuller_coeff_pos p _ n hn, WittVector.teichmuller_coeff_pos p _ n hn,
      zero_pow (Fact.out : p.Prime).ne_zero]

end Formalism.HermitianLattices.IntegralLatticeDensity
