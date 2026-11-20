import Mathlib

open scoped NNReal

namespace GlobalTheory

open WittVector in

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]`.
-/
theorem wittVector_iterate_frobenius_of_eq_pow {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    (y : WittVector l O) (h : frobenius y = y ^ l) (k : ℕ) :
    (WittVector.frobenius (p := l) (R := O))^[k] y = y ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]

open WittVector in

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ih, ← pow_mul, ← pow_succ]`.
-/
theorem wittVector_coeff_iterate_frobenius {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [CharP O l] (y : WittVector l O) (k n : ℕ) :
    ((WittVector.frobenius (p := l) (R := O))^[k] y).coeff n = y.coeff n ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ih, ← pow_mul, ← pow_succ]

open WittVector in

/- English proof (translation)
Introduce `l _ O _ _ _ y h`. Establish `hdiv : (l : WittVector l O) ∣ y - WittVector.teichmuller l (y.coeff 0)`. Establish `h0 : ∀ i < 1, (y - WittVector.teichmuller l (y.coeff 0)).coeff i = 0`. Introduce `i hi`. Take `rfl : i = 0` from `by omega`.

Establish `hc` using `map_sub (WittVector.constantCoeff (p := l) (R := O)) y (WittVector.teichmuller l (y.coeff 0))`. Simplify using `only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self] at hc`. Conclude with `hc`. Take `⟨w, hw⟩` from `(WittVector.frobenius_bijective l O).2 ((y - WittVector.teichmuller l (y.coeff 0)).shift 1)`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Rewrite using `[WittVector.eq_iterate_verschiebung h0, Function.iterate_one, ← hw, WittVector.verschiebung_frobenius, mul_comm]`. Use extensionality with `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[WittVector.teichmuller_coeff_pos l _ n hn]`.

Take `⟨c, hc⟩` from `dvd_sub_pow_of_dvd_sub hdiv n`. Establish `hy : y ^ l ^ n = WittVector.teichmuller l (y.coeff 0 ^ l ^ n) + c * (l : WittVector l O) ^ (n + 1)`. Rewrite using `[map_pow, mul_comm c]`. Conclude with `sub_eq_iff_eq_add'.mp hc`. Establish `hcoeff : (y ^ l ^ n).coeff n = 0`.

Rewrite using `[hy, WittVector.coeff_add_of_disjoint]`. Rewrite using `[WittVector.teichmuller_coeff_pos l _ n hn, WittVector.mul_pow_charP_coeff_zero _ (by omega : n < n + 1), add_zero]`. Introduce `m`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Conclude with `Or.inr (WittVector.mul_pow_charP_coeff_zero _ (by omega))`.

Conclude with `Or.inl (WittVector.teichmuller_coeff_pos l _ m hm)`. Rewrite `hcoeff` using `[← wittVector_iterate_frobenius_of_eq_pow y h n, wittVector_coeff_iterate_frobenius]`. Apply `(bijective_iterateFrobenius O l n).1` to reduce the goal to its premises. Use `show y.coeff n ^ l ^ n = (0 : O) ^ l ^ n`. Rewrite using `[hcoeff, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]`.
-/
theorem wittVector_eq_teichmuller_of_frobenius_eq_pow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] [PerfectRing O l]
      (y : WittVector l O), WittVector.frobenius y = y ^ l →
      y = WittVector.teichmuller l (y.coeff 0) := by
  intro l _ O _ _ _ y h

  have hdiv : (l : WittVector l O) ∣ y - WittVector.teichmuller l (y.coeff 0) := by
    have h0 : ∀ i < 1, (y - WittVector.teichmuller l (y.coeff 0)).coeff i = 0 := by
      intro i hi
      obtain rfl : i = 0 := by omega
      have hc := map_sub (WittVector.constantCoeff (p := l) (R := O)) y
        (WittVector.teichmuller l (y.coeff 0))
      simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self] at hc
      exact hc
    obtain ⟨w, hw⟩ := (WittVector.frobenius_bijective l O).2
      ((y - WittVector.teichmuller l (y.coeff 0)).shift 1)
    refine ⟨w, ?_⟩
    rw [WittVector.eq_iterate_verschiebung h0, Function.iterate_one, ← hw,
      WittVector.verschiebung_frobenius, mul_comm]
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [WittVector.teichmuller_coeff_pos l _ n hn]

  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub hdiv n
  have hy : y ^ l ^ n = WittVector.teichmuller l (y.coeff 0 ^ l ^ n) +
      c * (l : WittVector l O) ^ (n + 1) := by
    rw [map_pow, mul_comm c]
    exact sub_eq_iff_eq_add'.mp hc
  have hcoeff : (y ^ l ^ n).coeff n = 0 := by
    rw [hy, WittVector.coeff_add_of_disjoint]
    · rw [WittVector.teichmuller_coeff_pos l _ n hn,
        WittVector.mul_pow_charP_coeff_zero _ (by omega : n < n + 1), add_zero]
    · intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact Or.inr (WittVector.mul_pow_charP_coeff_zero _ (by omega))
      · exact Or.inl (WittVector.teichmuller_coeff_pos l _ m hm)

  rw [← wittVector_iterate_frobenius_of_eq_pow y h n, wittVector_coeff_iterate_frobenius] at hcoeff
  apply (bijective_iterateFrobenius O l n).1
  show y.coeff n ^ l ^ n = (0 : O) ^ l ^ n
  rw [hcoeff, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]

end GlobalTheory
