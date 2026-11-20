import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAutAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePow

noncomputable section

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog GlobalTheory.K5.Rel

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hi0 : i ≠ 0` using `by rintro rfl; exact hi (dvd_zero _)`. Take `⟨v, u, hu, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hi0 p hp.ne_one`. Establish `hv : v < n - m`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hi (Dvd.dvd.mul_right (pow_dvd_pow p h) _)`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Establish `hodd : Odd p` using `hp.odd_of_ne_two hp2`. Establish `hpm : 0 < p ^ m` using `pow_pos hp.pos m`.

Establish `hlt : 1 < 1 + p ^ m` using `by omega`. Establish `hnd : ¬ p ∣ 1 + p ^ m` using `fun h => hp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h)`. Establish `hval` using `padicValNat.pow_sub_pow (p := p) hodd (x := 1 + p ^ m) (y := 1) hlt (by rw [Nat.add_sub_cancel_left]; exact dvd_pow_self p (by omega)) hnd (n := p ^ (n - v - 1 - m)) (pow_ne_zero _ hp.ne_zero)`. Rewrite `hval` using `[one_pow, Nat.add_sub_cancel_left, padicValNat.prime_pow, padicValNat.prime_pow]`. Establish `hK1 : 1 < (1 + p ^ m) ^ (p ^ (n - v - 1 - m))` using `Nat.one_lt_pow (pow_ne_zero _ hp.ne_zero) hlt`.

Take `⟨e, d, hd, hed⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (Nat.sub_ne_zero_of_lt hK1) p hp.ne_one`. Establish `hd0 : d ≠ 0` using `by rintro rfl; exact hd (dvd_zero _)`. Rewrite `hval` using `[hed, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hd0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hd, add_zero]`. Establish `hK : (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) = 1 + p ^ e * d` using `by omega`. Use `⟨p ^ (n - v - 1 - m), d, u, hd, hu, ?_, p ^ (e - 1) * d, ?_⟩` and prove the remaining obligations.

Rewrite using `[hK, mul_add, mul_one, show n - 1 = v + e by omega, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hK, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]`.
-/
theorem exists_pow_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m n i : ℕ} (hm : 1 ≤ m)
    (hi : ¬ p ^ (n - m) ∣ i) :
    m < n ∧ ∃ K d u : ℕ, ¬ p ∣ d ∧ ¬ p ∣ u ∧ i * (1 + p ^ m) ^ K = i + u * d * p ^ (n - 1) ∧
      ∃ w, (1 + p ^ m) ^ K = 1 + p * w := by
  have hp : p.Prime := Fact.out
  have hi0 : i ≠ 0 := by rintro rfl; exact hi (dvd_zero _)
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 p hp.ne_one
  have hv : v < n - m := by
    by_contra h
    push_neg at h
    exact hi (Dvd.dvd.mul_right (pow_dvd_pow p h) _)
  refine ⟨by omega, ?_⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpm : 0 < p ^ m := pow_pos hp.pos m
  have hlt : 1 < 1 + p ^ m := by omega
  have hnd : ¬ p ∣ 1 + p ^ m := fun h =>
    hp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h)
  have hval := padicValNat.pow_sub_pow (p := p) hodd (x := 1 + p ^ m) (y := 1) hlt
    (by rw [Nat.add_sub_cancel_left]; exact dvd_pow_self p (by omega)) hnd
    (n := p ^ (n - v - 1 - m)) (pow_ne_zero _ hp.ne_zero)
  rw [one_pow, Nat.add_sub_cancel_left, padicValNat.prime_pow, padicValNat.prime_pow] at hval
  have hK1 : 1 < (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) :=
    Nat.one_lt_pow (pow_ne_zero _ hp.ne_zero) hlt
  obtain ⟨e, d, hd, hed⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.sub_ne_zero_of_lt hK1) p
    hp.ne_one
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
  rw [hed, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hd0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hd, add_zero] at hval
  have hK : (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) = 1 + p ^ e * d := by omega
  refine ⟨p ^ (n - v - 1 - m), d, u, hd, hu, ?_, p ^ (e - 1) * d, ?_⟩
  · rw [hK, mul_add, mul_one, show n - 1 = v + e by omega, pow_add]
    ring
  · rw [hK, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]

end GlobalTheory.K5.MonX

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog GlobalTheory.K5.Rel

end GlobalTheory.K5.MonX

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog GlobalTheory.K5.Rel

end GlobalTheory.K5.MonX
