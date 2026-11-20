import Mathlib

open Polynomial Matrix

/- English proof (translation)
Introduce `R _ _ _ p _ _ x n hn hx hxn`. Establish `hp : p.Prime` using `Fact.out`. Take `⟨k, m, hpm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one`. Establish `hy1 : x ^ p ^ k - 1 = (x - 1) ^ p ^ k` using `by rw [sub_pow_char_pow, one_pow]`. Establish `hym : (x ^ p ^ k) ^ m = 1` using `by rw [← pow_mul]; exact hxn`.

Establish `hyM : x ^ p ^ k - 1 ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[hy1]`. Conclude with `Ideal.pow_mem_of_mem _ hx _ (pow_pos hp.pos _)`. Establish `hmu : IsUnit (m : R)`. Establish `h0 : (m : ZMod p) ≠ 0` using `by rwa [Ne, ZMod.natCast_eq_zero_iff]`.

Establish `h` using `(Ne.isUnit h0).map (ZMod.castHom (dvd_refl p) R)`. Simplify using `using h`. Establish `hs : (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i) - m ∈ IsLocalRing.maximalIdeal R`. Establish `h : (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i) - m = ∑ i ∈ Finset.range m, ((x ^ p ^ k) ^ i - 1)`. Simplify using `[Finset.sum_sub_distrib]`.

Rewrite using `[h]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `sub_dvd_pow_sub_pow (x ^ p ^ k) 1 i`. Rewrite `hc` using `[one_pow]`. Rewrite using `[hc]`.

Conclude with `Ideal.mul_mem_right _ _ hyM`. Establish `hsu : IsUnit (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i)`. Assume the negation of the conclusion as `h`. Establish `h'` using `(IsLocalRing.mem_maximalIdeal _).2 h`. Establish `h2` using `Ideal.sub_mem _ h' hs`.

Rewrite `h2` using `[sub_sub_cancel]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h2 hmu`. Establish `hy0 : x ^ p ^ k - 1 = 0`. Establish `h` using `geom_sum_mul (x ^ p ^ k) m`. Rewrite `h` using `[hym, sub_self]`.

Conclude with `hsu.mul_right_eq_zero.1 h`. Rewrite `hy0` using `[hy1]`. Conclude with `sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hp.ne_zero)).1 hy0)`.
-/
theorem UpperTheory.V.Pr.T.oneUnitTF :
    ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (x : R) (n : ℕ),
      n ≠ 0 → x - 1 ∈ IsLocalRing.maximalIdeal R → x ^ n = 1 → x = 1 := by
  intro R _ _ _ p _ _ x n hn hx hxn
  have hp : p.Prime := Fact.out
  obtain ⟨k, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hy1 : x ^ p ^ k - 1 = (x - 1) ^ p ^ k := by rw [sub_pow_char_pow, one_pow]
  have hym : (x ^ p ^ k) ^ m = 1 := by rw [← pow_mul]; exact hxn
  have hyM : x ^ p ^ k - 1 ∈ IsLocalRing.maximalIdeal R := by
    rw [hy1]; exact Ideal.pow_mem_of_mem _ hx _ (pow_pos hp.pos _)
  have hmu : IsUnit (m : R) := by
    have h0 : (m : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have h := (Ne.isUnit h0).map (ZMod.castHom (dvd_refl p) R)
    simpa using h
  have hs : (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i) - m ∈ IsLocalRing.maximalIdeal R := by
    have h : (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i) - m
        = ∑ i ∈ Finset.range m, ((x ^ p ^ k) ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [h]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (x ^ p ^ k) 1 i
    rw [one_pow] at hc
    rw [hc]
    exact Ideal.mul_mem_right _ _ hyM
  have hsu : IsUnit (∑ i ∈ Finset.range m, (x ^ p ^ k) ^ i) := by
    by_contra h
    have h' := (IsLocalRing.mem_maximalIdeal _).2 h
    have h2 := Ideal.sub_mem _ h' hs
    rw [sub_sub_cancel] at h2
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 hmu
  have hy0 : x ^ p ^ k - 1 = 0 := by
    have h := geom_sum_mul (x ^ p ^ k) m
    rw [hym, sub_self] at h
    exact hsu.mul_right_eq_zero.1 h
  rw [hy1] at hy0
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hp.ne_zero)).1 hy0)
