import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum IsOrbit)

/- English proof (translation)
Introduce `l g d j Y hl hd hg hY h1 h2 h3`. Establish `hj : j ≤ padicValNat l (g ^ d - 1)`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `h5` using `h3 _ hlt`.

Establish `h4 : g ≤ g ^ d` using `Nat.le_self_pow (by omega) g`. Establish `h6 : (l : ℝ) ^ (4 * padicValNat l (g ^ d - 1)) ≤ (g : ℝ)` using `h5.trans hY`. Establish `h7 : l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g` using `by exact_mod_cast h6`. Use linear arithmetic over natural numbers and integers. Conclude with `(pow_dvd_pow l hj).trans pow_padicValNat_dvd`.
-/
theorem bad_primes_divides : BBDivides := by
  intro l g d j Y hl hd hg hY h1 h2 h3
  have hj : j ≤ padicValNat l (g ^ d - 1) := by
    by_contra hlt
    push Not at hlt
    have h5 := h3 _ hlt
    have h4 : g ≤ g ^ d := Nat.le_self_pow (by omega) g
    have h6 : (l : ℝ) ^ (4 * padicValNat l (g ^ d - 1)) ≤ (g : ℝ) := h5.trans hY
    have h7 : l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g := by exact_mod_cast h6
    omega
  exact (pow_dvd_pow l hj).trans pow_padicValNat_dvd

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
