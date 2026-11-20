import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Mathlib.NumberTheory.Multiplicity

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

/- English proof (translation)
Use `haveI := Fact.mk hl`. Establish `hpow1 : 1 ≤ l ^ c` using `Nat.one_le_pow c l hl.pos`. Establish `hx1 : 1 < 1 + l ^ c` using `by omega`. Establish `hdvd : l ∣ (1 + l ^ c) - 1`. Rewrite using `[Nat.add_sub_cancel_left]`.

Conclude with `dvd_pow_self l (by omega)`. Establish `hnd : ¬ l ∣ 1 + l ^ c`. Introduce `h`. Rewrite `h` using `[add_comm]`. Use `(Nat.dvd_add_right (dvd_pow_self l (by omega : c ≠ 0))).1 h` as an intermediate fact.

Conclude with `hl.one_lt.ne' (Nat.dvd_one.1 this)`. Break down `hl.eq_two_or_odd' with rfl | hodd` into its components or cases. Take `⟨d, rfl⟩ : ∃ d, c = d + 2` from `⟨c - 2, by have := h2 rfl; omega⟩`. Establish `h4 : 2 ^ (d + 2) = 4 * 2 ^ d` using `by ring`. Establish `h` using `padicValNat.pow_two_sub_pow (x := 1 + 2 ^ (d + 2)) (y := 1) hx1 hdvd hnd (n := 2 * m) (by omega) (even_two_mul m)`.

Rewrite `h` using `[one_pow]`. Establish `hA : padicValNat 2 (1 + 2 ^ (d + 2) + 1) = 1`. Establish `e : 1 + 2 ^ (d + 2) + 1 = 2 * (1 + 2 * 2 ^ d)` using `by rw [h4]; ring`. Rewrite using `[e, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by omega)]`. Establish `hB : padicValNat 2 (1 + 2 ^ (d + 2) - 1) = d + 2`.

Rewrite using `[Nat.add_sub_cancel_left, padicValNat.prime_pow]`. Establish `hC : padicValNat 2 (2 * m) = 1 + padicValNat 2 m`. Rewrite using `[padicValNat.mul (by norm_num) hm, padicValNat.self (by norm_num)]`. Establish `hxm : 1 < (1 + 2 ^ (d + 2)) ^ m` using `Nat.one_lt_pow hm hx1`. Take `⟨b, hb⟩ : ∃ b, (1 + 2 ^ (d + 2)) ^ m = b + 1` from `⟨_ - 1, (Nat.sub_add_cancel hxm.le).symm⟩`.

Establish `hmod : (1 + 2 ^ (d + 2)) ^ m % 4 = 1`. Rewrite using `[Nat.pow_mod, h4]`. Establish `: (1 + 4 * 2 ^ d) % 4 = 1` using `by omega`. Rewrite using `[this, one_pow]`. Both sides reduce to the same expression.

Establish `hD : padicValNat 2 ((1 + 2 ^ (d + 2)) ^ m + 1) = 1`. Take `⟨q, hq⟩ : ∃ q, (1 + 2 ^ (d + 2)) ^ m + 1 = 2 * (2 * q + 1)` from `⟨((1 + 2 ^ (d + 2)) ^ m + 1) / 4, by omega⟩`. Rewrite using `[hq, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by omega)]`. Establish `hfac : (1 + 2 ^ (d + 2)) ^ (2 * m) - 1 = ((1 + 2 ^ (d + 2)) ^ m - 1) * ((1 + 2 ^ (d + 2)) ^ m + 1)`. Rewrite using `[pow_mul', hb, Nat.add_sub_cancel]`.

Establish `: (b + 1) ^ 2 = b * (b + 1 + 1) + 1` using `by ring`. Rewrite using `[this, Nat.add_sub_cancel]`. Rewrite `h` using `[hfac, padicValNat.mul (by omega) (by omega), hD, hA, hB, hC]`. Use linear arithmetic over natural numbers and integers. Use `padicValNat.pow_sub_pow hodd hx1 hdvd hnd hm` as an intermediate fact.

Rewrite `this` using `[one_pow, Nat.add_sub_cancel_left, padicValNat.prime_pow]`. Then use the resulting hypothesis.
-/
private theorem padic_val_one_add_pow_sub_one (l c m : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (h2 : l = 2 → 2 ≤ c)
    (hm : m ≠ 0) : padicValNat l ((1 + l ^ c) ^ m - 1) = c + padicValNat l m := by
  haveI := Fact.mk hl
  have hpow1 : 1 ≤ l ^ c := Nat.one_le_pow c l hl.pos
  have hx1 : 1 < 1 + l ^ c := by omega
  have hdvd : l ∣ (1 + l ^ c) - 1 := by
    rw [Nat.add_sub_cancel_left]
    exact dvd_pow_self l (by omega)
  have hnd : ¬ l ∣ 1 + l ^ c := by
    intro h
    rw [add_comm] at h
    have := (Nat.dvd_add_right (dvd_pow_self l (by omega : c ≠ 0))).1 h
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hl.eq_two_or_odd' with rfl | hodd
  · obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by have := h2 rfl; omega⟩
    have h4 : 2 ^ (d + 2) = 4 * 2 ^ d := by ring
    have h := padicValNat.pow_two_sub_pow (x := 1 + 2 ^ (d + 2)) (y := 1) hx1 hdvd hnd
      (n := 2 * m) (by omega) (even_two_mul m)
    rw [one_pow] at h
    have hA : padicValNat 2 (1 + 2 ^ (d + 2) + 1) = 1 := by
      have e : 1 + 2 ^ (d + 2) + 1 = 2 * (1 + 2 * 2 ^ d) := by rw [h4]; ring
      rw [e, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by omega)]
    have hB : padicValNat 2 (1 + 2 ^ (d + 2) - 1) = d + 2 := by
      rw [Nat.add_sub_cancel_left, padicValNat.prime_pow]
    have hC : padicValNat 2 (2 * m) = 1 + padicValNat 2 m := by
      rw [padicValNat.mul (by norm_num) hm, padicValNat.self (by norm_num)]
    have hxm : 1 < (1 + 2 ^ (d + 2)) ^ m := Nat.one_lt_pow hm hx1
    obtain ⟨b, hb⟩ : ∃ b, (1 + 2 ^ (d + 2)) ^ m = b + 1 := ⟨_ - 1, (Nat.sub_add_cancel hxm.le).symm⟩
    have hmod : (1 + 2 ^ (d + 2)) ^ m % 4 = 1 := by
      rw [Nat.pow_mod, h4]
      have : (1 + 4 * 2 ^ d) % 4 = 1 := by omega
      rw [this, one_pow]
      rfl
    have hD : padicValNat 2 ((1 + 2 ^ (d + 2)) ^ m + 1) = 1 := by
      obtain ⟨q, hq⟩ : ∃ q, (1 + 2 ^ (d + 2)) ^ m + 1 = 2 * (2 * q + 1) :=
        ⟨((1 + 2 ^ (d + 2)) ^ m + 1) / 4, by omega⟩
      rw [hq, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by omega)]
    have hfac : (1 + 2 ^ (d + 2)) ^ (2 * m) - 1 =
        ((1 + 2 ^ (d + 2)) ^ m - 1) * ((1 + 2 ^ (d + 2)) ^ m + 1) := by
      rw [pow_mul', hb, Nat.add_sub_cancel]
      have : (b + 1) ^ 2 = b * (b + 1 + 1) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
    rw [hfac, padicValNat.mul (by omega) (by omega), hD, hA, hB, hC] at h
    omega
  · have := padicValNat.pow_sub_pow hodd hx1 hdvd hnd hm
    rwa [one_pow, Nat.add_sub_cancel_left, padicValNat.prime_pow] at this

/- English proof (translation)
Introduce `l c ν E hl hc h2 hcν hE`. Use `haveI := Fact.mk hl`. Establish `hE0 : E ≠ 0` using `by omega`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: 2 ≤ 1 + l ^ c` using `by have := Nat.one_le_pow c l hl.pos; omega`.

Conclude with `this.trans (Nat.le_self_pow hE0 _)`. Rewrite using `[Nat.factorization_def _ hl, Nat.factorization_def _ hl]`. Conclude with `padic_val_one_add_pow_sub_one l c E hl hc h2 hE0`. Rewrite using `[Nat.factorization_def _ hl, Nat.factorization_def _ hl, ← pow_mul, padic_val_one_add_pow_sub_one l c _ hl hc h2 (mul_ne_zero hE0 (pow_ne_zero _ hl.ne_zero)), padicValNat.mul hE0 (pow_ne_zero _ hl.ne_zero), padicValNat.prime_pow]`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.ZK.Ct.lte :
    ∀ l c ν E : ℕ, l.Prime → 1 ≤ c → (l = 2 → 2 ≤ c) → c ≤ ν → 1 ≤ E → 2 ≤ (1 + l ^ c) ^ E ∧ ((1 + l ^ c) ^ E - 1).factorization l = c + E.factorization l ∧ (((1 + l ^ c) ^ E) ^ l ^ (ν - c) - 1).factorization l = ν + E.factorization l := by
  intro l c ν E hl hc h2 hcν hE
  haveI := Fact.mk hl
  have hE0 : E ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · have : 2 ≤ 1 + l ^ c := by have := Nat.one_le_pow c l hl.pos; omega
    exact this.trans (Nat.le_self_pow hE0 _)
  · rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl]
    exact padic_val_one_add_pow_sub_one l c E hl hc h2 hE0
  · rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl, ← pow_mul,
      padic_val_one_add_pow_sub_one l c _ hl hc h2 (mul_ne_zero hE0 (pow_ne_zero _ hl.ne_zero)),
      padicValNat.mul hE0 (pow_ne_zero _ hl.ne_zero), padicValNat.prime_pow]
    omega
