import Mathlib

namespace Formalism.MainNotions.UnusedSlot80.LTE

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℚ))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero, AddValuation.map_zero]`. Conclude with `le_top`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ]`.

Conclude with `le_trans (le_min ih (le_of_eq v.map_one.symm)) (v.map_add _ _)`.
-/
theorem natCast_nonneg (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero, AddValuation.map_zero]; exact le_top
  | succ n ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (le_of_eq v.map_one.symm)) (v.map_add _ _)

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg m`. Rewrite using `[Int.cast_natCast]`. Conclude with `natCast_nonneg v n`. Rewrite using `[Int.cast_neg, Int.cast_natCast, AddValuation.map_neg]`. Conclude with `natCast_nonneg v n`.
-/
theorem intCast_nonneg (m : ℤ) : 0 ≤ v (m : K) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [Int.cast_natCast]; exact natCast_nonneg v n
  · rw [Int.cast_neg, Int.cast_natCast, AddValuation.map_neg]; exact natCast_nonneg v n

/- English proof (translation)
Conclude with `(zero_lt_one : (0 : ℚ) < 1)` after adjusting the coercions.
-/
private theorem withTop_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)

/- English proof (translation)
Establish `hcop : Nat.Coprime p m` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hm`. Establish `h1 : ((Nat.gcd p m : ℕ) : ℤ) = (p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m` using `Nat.gcd_eq_gcd_ab p m`. Rewrite `h1` using `[hcop.gcd_eq_one]`. Establish `hK : (1 : K) = (p : K) * (Nat.gcdA p m : K) + (m : K) * (Nat.gcdB p m : K)`. Establish `h2` using `congrArg (fun z : ℤ => (z : K)) h1`.

Move the coercions through the operations in `at h2`. Conclude with `h2`. Establish `h0` using `natCast_nonneg v m`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < v (m : K)` using `lt_of_le_of_ne h0 (Ne.symm hne)`.

Establish `h3 : 0 < v ((p : K) * (Nat.gcdA p m : K))`. Rewrite using `[AddValuation.map_mul, hv]`. Conclude with `lt_of_lt_of_le withTop_zero_lt_one (le_add_of_nonneg_right (intCast_nonneg v _))`. Establish `h4 : 0 < v ((m : K) * (Nat.gcdB p m : K))`. Rewrite using `[AddValuation.map_mul]`.

Conclude with `lt_of_lt_of_le hpos (le_add_of_nonneg_right (intCast_nonneg v _))`. Establish `h5` using `v.map_add ((p : K) * (Nat.gcdA p m : K)) ((m : K) * (Nat.gcdB p m : K))`. Rewrite `h5` using `[← hK, AddValuation.map_one]`. Conclude with `absurd h5 (not_le.2 (lt_min h3 h4))`.
-/
theorem natCast_eq_zero_of_not_dvd {p : ℕ} (hp : p.Prime) (hv : v (p : K) = 1) {m : ℕ}
    (hm : ¬ p ∣ m) : v (m : K) = 0 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have h1 : ((Nat.gcd p m : ℕ) : ℤ) = (p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m :=
    Nat.gcd_eq_gcd_ab p m
  rw [hcop.gcd_eq_one] at h1
  have hK : (1 : K) = (p : K) * (Nat.gcdA p m : K) + (m : K) * (Nat.gcdB p m : K) := by
    have h2 := congrArg (fun z : ℤ => (z : K)) h1
    push_cast at h2
    exact h2
  have h0 := natCast_nonneg v m
  by_contra hne
  have hpos : 0 < v (m : K) := lt_of_le_of_ne h0 (Ne.symm hne)
  have h3 : 0 < v ((p : K) * (Nat.gcdA p m : K)) := by
    rw [AddValuation.map_mul, hv]
    exact lt_of_lt_of_le withTop_zero_lt_one (le_add_of_nonneg_right (intCast_nonneg v _))
  have h4 : 0 < v ((m : K) * (Nat.gcdB p m : K)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_right (intCast_nonneg v _))
  have h5 := v.map_add ((p : K) * (Nat.gcdA p m : K)) ((m : K) * (Nat.gcdB p m : K))
  rw [← hK, AddValuation.map_one] at h5
  exact absurd h5 (not_le.2 (lt_min h3 h4))

/- English proof (translation)
Rewrite using `[AddValuation.map_pow]`. Conclude with `nsmul_nonneg hx k`.
-/
theorem pow_nonneg' {x : K} (hx : 0 ≤ v x) (k : ℕ) : 0 ≤ v (x ^ k) := by
  rw [AddValuation.map_pow]
  exact nsmul_nonneg hx k

/- English proof (translation)
The claim follows from `Finset.sum_induction f (fun y => 0 ≤ v y) (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b)) (by rw [AddValuation.map_zero]; exact le_top) h`.
-/
private theorem v_finset_sum_nonneg_of_forall {ι : Type*} (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, 0 ≤ v (f i)) : 0 ≤ v (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun y => 0 ≤ v y)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b))
    (by rw [AddValuation.map_zero]; exact le_top) h

/- English proof (translation)
The claim follows from `v_finset_sum_nonneg_of_forall v _ _ (fun j _ => pow_nonneg' v hx j)`.
-/
theorem geom_nonneg {x : K} (hx : 0 ≤ v x) (k : ℕ) : 0 ≤ v (∑ j ∈ Finset.range k, x ^ j) :=
  v_finset_sum_nonneg_of_forall v _ _ (fun j _ => pow_nonneg' v hx j)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h1` using `v.map_add (a + b) (-b)`. Rewrite `h1` using `[AddValuation.map_neg, add_neg_cancel_right]`. Break down `min_le_iff.1 h1 with h2 | h2` into its components or cases. Conclude with `h2`.

Conclude with `absurd h2 (not_le.2 h)`. Conclude with `le_trans (le_min le_rfl h.le) (v.map_add a b)`.
-/
private theorem v_add_eq_left_of_v_lt {a b : K} (h : v a < v b) : v (a + b) = v a := by
  apply le_antisymm
  · have h1 := v.map_add (a + b) (-b)
    rw [AddValuation.map_neg, add_neg_cancel_right] at h1
    rcases min_le_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)
  · exact le_trans (le_min le_rfl h.le) (v.map_add a b)

/- English proof (translation)
Establish `h1` using `v_add_eq_left_of_v_lt v (a := 1) (b := x - 1) (by rw [AddValuation.map_one]; exact hy)`. Rewrite `h1` using `[show (1 : K) + (x - 1) = x by ring, AddValuation.map_one]`. Then use the resulting hypothesis.
-/
theorem v_x_zero {x : K} (hy : 0 < v (x - 1)) : v x = 0 := by
  have h1 := v_add_eq_left_of_v_lt v (a := 1) (b := x - 1) (by rw [AddValuation.map_one]; exact hy)
  rwa [show (1 : K) + (x - 1) = x by ring, AddValuation.map_one] at h1

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Establish `h1 : ∀ j ∈ Finset.range k, (x - 1) * ∑ i ∈ Finset.range j, x ^ i = x ^ j - 1` using `fun j _ => by rw [mul_comm, geom_sum_mul]`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_sub_distrib]`. Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem geom_expand (x : K) (k : ℕ) :
    ∑ j ∈ Finset.range k, x ^ j =
      (k : K) + (x - 1) * ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range j, x ^ i := by
  rw [Finset.mul_sum]
  have h1 : ∀ j ∈ Finset.range k, (x - 1) * ∑ i ∈ Finset.range j, x ^ i = x ^ j - 1 :=
    fun j _ => by rw [mul_comm, geom_sum_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/- English proof (translation)
Establish `hx : 0 ≤ v x` using `(v_x_zero v hy).ge`. Establish `hm0 : v (m : K) = 0` using `natCast_eq_zero_of_not_dvd v hp hv hm`. Establish `hlt : v (m : K) < v ((x - 1) * ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, x ^ i)`. Rewrite using `[hm0, AddValuation.map_mul]`. Conclude with `lt_of_lt_of_le hy (le_add_of_nonneg_right (v_finset_sum_nonneg_of_forall v _ _ (fun j _ => geom_nonneg v hx j)))`.

Establish `hS : v (∑ j ∈ Finset.range m, x ^ j) = 0`. Rewrite using `[geom_expand, v_add_eq_left_of_v_lt v hlt, hm0]`. Rewrite using `[← geom_sum_mul x m, AddValuation.map_mul, hS, zero_add]`.
-/
theorem val_pow_sub_one_coprime {p : ℕ} (hp : p.Prime) (hv : v (p : K) = 1) {x : K}
    (hy : 0 < v (x - 1)) {m : ℕ} (hm : ¬ p ∣ m) : v (x ^ m - 1) = v (x - 1) := by
  have hx : 0 ≤ v x := (v_x_zero v hy).ge
  have hm0 : v (m : K) = 0 := natCast_eq_zero_of_not_dvd v hp hv hm
  have hlt : v (m : K) <
      v ((x - 1) * ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range j, x ^ i) := by
    rw [hm0, AddValuation.map_mul]
    exact lt_of_lt_of_le hy (le_add_of_nonneg_right
      (v_finset_sum_nonneg_of_forall v _ _ (fun j _ => geom_nonneg v hx j)))
  have hS : v (∑ j ∈ Finset.range m, x ^ j) = 0 := by
    rw [geom_expand, v_add_eq_left_of_v_lt v hlt, hm0]
  rw [← geom_sum_mul x m, AddValuation.map_mul, hS, zero_add]

/- English proof (translation)
Conclude with `(by norm_num : (1 : ℚ) < 1 + 1)` after adjusting the coercions.
-/
private theorem withTop_one_lt_one_add_one : (1 : WithTop ℚ) < 1 + 1 := by
  exact_mod_cast (by norm_num : (1 : ℚ) < 1 + 1)

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Rewrite using `[Nat.cast_mul, AddValuation.map_mul, hv]`. Conclude with `le_add_of_nonneg_right (natCast_nonneg v c)`.
-/
private theorem one_le_v_natCast_of_dvd {p : ℕ} (hv : v (p : K) = 1) {n : ℕ} (h : p ∣ n) :
    1 ≤ v (n : K) := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, AddValuation.map_mul, hv]
  exact le_add_of_nonneg_right (natCast_nonneg v c)

/- English proof (translation)
Establish `hx : 0 ≤ v x` using `(v_x_zero v (lt_of_lt_of_le withTop_zero_lt_one hy)).ge`. Establish `hid : ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, x ^ i = (∑ j ∈ Finset.range p, (j : K)) + (x - 1) * ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun j _ => geom_expand x j)`. Establish `hN : 1 ≤ v (∑ j ∈ Finset.range p, (j : K))`.

Rewrite using `[show (∑ j ∈ Finset.range p, (j : K)) = ((∑ j ∈ Finset.range p, j : ℕ) : K) by`. Rewrite using `[Nat.cast_sum]]`. Apply `one_le_v_natCast_of_dvd v hv` to reduce the goal to its premises. Establish `hd : p ∣ (∑ i ∈ Finset.range p, i) * 2`. Rewrite using `[Finset.sum_range_id_mul_two]`.

Conclude with `dvd_mul_right p (p - 1)`. Break down `(Nat.Prime.dvd_mul hp).1 hd with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2`. Establish `hT : 0 ≤ v (∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l)` using `v_finset_sum_nonneg_of_forall v _ _ (fun j _ => v_finset_sum_nonneg_of_forall v _ _ (fun i _ => geom_nonneg v hx i))`.

Establish `hinner : 1 ≤ v ((∑ j ∈ Finset.range p, (j : K)) + (x - 1) * ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l)`. Use `le_trans (le_min hN ?_) (v.map_add _ _)` and prove the remaining obligations. Rewrite using `[AddValuation.map_mul]`. Conclude with `le_trans hy (le_add_of_nonneg_right hT)`. Establish `hlt : v (p : K) < v ((x - 1) * ((∑ j ∈ Finset.range p, (j : K)) + (x - 1) * ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l))`.

Rewrite using `[hv, AddValuation.map_mul]`. Conclude with `lt_of_lt_of_le withTop_one_lt_one_add_one (add_le_add hy hinner)`. Establish `hsum : v (∑ j ∈ Finset.range p, x ^ j) = 1`. Rewrite using `[geom_expand, hid, v_add_eq_left_of_v_lt v hlt, hv]`. Rewrite using `[← geom_sum_mul x p, AddValuation.map_mul, hsum, add_comm]`.
-/
theorem val_pow_p_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hv : v (p : K) = 1) {x : K}
    (hy : 1 ≤ v (x - 1)) : v (x ^ p - 1) = v (x - 1) + 1 := by
  have hx : 0 ≤ v x := (v_x_zero v (lt_of_lt_of_le withTop_zero_lt_one hy)).ge
  have hid : ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, x ^ i =
      (∑ j ∈ Finset.range p, (j : K)) + (x - 1) *
        ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => geom_expand x j)
  have hN : 1 ≤ v (∑ j ∈ Finset.range p, (j : K)) := by
    rw [show (∑ j ∈ Finset.range p, (j : K)) = ((∑ j ∈ Finset.range p, j : ℕ) : K) by
      rw [Nat.cast_sum]]
    apply one_le_v_natCast_of_dvd v hv
    have hd : p ∣ (∑ i ∈ Finset.range p, i) * 2 := by
      rw [Finset.sum_range_id_mul_two]
      exact dvd_mul_right p (p - 1)
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
  have hT : 0 ≤ v (∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l) :=
    v_finset_sum_nonneg_of_forall v _ _
      (fun j _ => v_finset_sum_nonneg_of_forall v _ _ (fun i _ => geom_nonneg v hx i))
  have hinner : 1 ≤ v ((∑ j ∈ Finset.range p, (j : K)) + (x - 1) *
      ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l) := by
    refine le_trans (le_min hN ?_) (v.map_add _ _)
    rw [AddValuation.map_mul]
    exact le_trans hy (le_add_of_nonneg_right hT)
  have hlt : v (p : K) < v ((x - 1) * ((∑ j ∈ Finset.range p, (j : K)) + (x - 1) *
      ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ∑ l ∈ Finset.range i, x ^ l)) := by
    rw [hv, AddValuation.map_mul]
    exact lt_of_lt_of_le withTop_one_lt_one_add_one (add_le_add hy hinner)
  have hsum : v (∑ j ∈ Finset.range p, x ^ j) = 1 := by
    rw [geom_expand, hid, v_add_eq_left_of_v_lt v hlt, hv]
  rw [← geom_sum_mul x p, AddValuation.map_mul, hsum, add_comm]

/- English proof (translation)
Conclude with `(Nat.cast_nonneg k : (0 : ℚ) ≤ k)` after adjusting the coercions.
-/
private theorem withTop_rat_natCast_nonneg (k : ℕ) : (0 : WithTop ℚ) ≤ (k : WithTop ℚ) := by
  exact_mod_cast (Nat.cast_nonneg k : (0 : ℚ) ≤ k)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hk : 1 ≤ v (x ^ (p ^ k) - 1)`. Rewrite using `[ih]`.

Conclude with `le_trans hy (le_add_of_nonneg_right (withTop_rat_natCast_nonneg k))`. Rewrite using `[pow_succ p k, pow_mul x (p ^ k) p, val_pow_p_sub_one v hp hp2 hv hk, ih, Nat.cast_succ, add_assoc]`.
-/
theorem val_pow_pk_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hv : v (p : K) = 1) {x : K}
    (hy : 1 ≤ v (x - 1)) (k : ℕ) : v (x ^ (p ^ k) - 1) = v (x - 1) + (k : WithTop ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 1 ≤ v (x ^ (p ^ k) - 1) := by
      rw [ih]
      exact le_trans hy (le_add_of_nonneg_right (withTop_rat_natCast_nonneg k))
    rw [pow_succ p k, pow_mul x (p ^ k) p, val_pow_p_sub_one v hp hp2 hv hk, ih,
      Nat.cast_succ, add_assoc]

/- English proof (translation)
Use `haveI := Fact.mk hp`. Take `⟨n, hn⟩` from `(pow_padicValNat_dvd : p ^ padicValNat p m ∣ m)`. Establish `hpn : ¬ p ∣ n`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `pow_succ_padicValNat_not_dvd hm ⟨c, hn.trans (by ring)⟩`.

Establish `key : x ^ m = (x ^ (p ^ padicValNat p m)) ^ n`. Rewrite using `[← pow_mul, ← hn]`. Establish `hz` using `val_pow_pk_sub_one v hp hp2 hv hy (padicValNat p m)`. Establish `hzpos : 0 < v (x ^ (p ^ padicValNat p m) - 1)`. Rewrite using `[hz]`.

Conclude with `lt_of_lt_of_le withTop_zero_lt_one (le_trans hy (le_add_of_nonneg_right (withTop_rat_natCast_nonneg _)))`. Rewrite using `[key, val_pow_sub_one_coprime v hp hv hzpos hpn, hz]`.
-/
theorem val_pow_sub_one_nat {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hv : v (p : K) = 1) {x : K}
    (hy : 1 ≤ v (x - 1)) {m : ℕ} (hm : m ≠ 0) :
    v (x ^ m - 1) = v (x - 1) + (padicValNat p m : WithTop ℚ) := by
  haveI := Fact.mk hp
  obtain ⟨n, hn⟩ := (pow_padicValNat_dvd : p ^ padicValNat p m ∣ m)
  have hpn : ¬ p ∣ n := by
    rintro ⟨c, rfl⟩
    exact pow_succ_padicValNat_not_dvd hm ⟨c, hn.trans (by ring)⟩
  have key : x ^ m = (x ^ (p ^ padicValNat p m)) ^ n := by
    rw [← pow_mul, ← hn]
  have hz := val_pow_pk_sub_one v hp hp2 hv hy (padicValNat p m)
  have hzpos : 0 < v (x ^ (p ^ padicValNat p m) - 1) := by
    rw [hz]
    exact lt_of_lt_of_le withTop_zero_lt_one
      (le_trans hy (le_add_of_nonneg_right (withTop_rat_natCast_nonneg _)))
  rw [key, val_pow_sub_one_coprime v hp hv hzpos hpn, hz]

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg m`. Establish `hn : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm rfl`. Establish `hpv : padicValInt p (n : ℤ) = padicValNat p n` using `by simp [padicValInt]`.

Rewrite using `[zpow_natCast, hpv]`. Conclude with `val_pow_sub_one_nat v hp hp2 hv hy hn`. Establish `hn : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (by simp)`.

Establish `hpv : padicValInt p (-(n : ℤ)) = padicValNat p n` using `by simp [padicValInt]`. Establish `hvx : v x = 0` using `v_x_zero v (lt_of_lt_of_le withTop_zero_lt_one hy)`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hvx` using `[AddValuation.map_zero]`.

Simplify using `at hvx`. Establish `hxn : x ^ n ≠ 0` using `pow_ne_zero n hx0`. Establish `hvxn : v (x ^ n) = 0`. Rewrite using `[AddValuation.map_pow, hvx, smul_zero]`. Establish `hinv : v ((x ^ n)⁻¹) = 0`.

Establish `h1 : v ((x ^ n)⁻¹) + v (x ^ n) = 0`. Rewrite using `[← AddValuation.map_mul, inv_mul_cancel₀ hxn, AddValuation.map_one]`. Rewrite `h1` using `[hvxn, add_zero]`. Then use the resulting hypothesis. Establish `hrw : x ^ (-(n : ℤ)) - 1 = -((x ^ n)⁻¹ * (x ^ n - 1))`. Rewrite using `[zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hxn, mul_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrw, AddValuation.map_neg, AddValuation.map_mul, hinv, zero_add, hpv]`. Conclude with `val_pow_sub_one_nat v hp hp2 hv hy hn`.
-/
theorem val_zpow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hv : v (p : K) = 1) {x : K}
    (hy : 1 ≤ v (x - 1)) {m : ℤ} (hm : m ≠ 0) :
    v (x ^ m - 1) = v (x - 1) + (padicValInt p m : WithTop ℚ) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hm rfl
    have hpv : padicValInt p (n : ℤ) = padicValNat p n := by simp [padicValInt]
    rw [zpow_natCast, hpv]
    exact val_pow_sub_one_nat v hp hp2 hv hy hn
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hm (by simp)
    have hpv : padicValInt p (-(n : ℤ)) = padicValNat p n := by simp [padicValInt]
    have hvx : v x = 0 := v_x_zero v (lt_of_lt_of_le withTop_zero_lt_one hy)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [AddValuation.map_zero] at hvx
      simp at hvx
    have hxn : x ^ n ≠ 0 := pow_ne_zero n hx0
    have hvxn : v (x ^ n) = 0 := by
      rw [AddValuation.map_pow, hvx, smul_zero]
    have hinv : v ((x ^ n)⁻¹) = 0 := by
      have h1 : v ((x ^ n)⁻¹) + v (x ^ n) = 0 := by
        rw [← AddValuation.map_mul, inv_mul_cancel₀ hxn, AddValuation.map_one]
      rwa [hvxn, add_zero] at h1
    have hrw : x ^ (-(n : ℤ)) - 1 = -((x ^ n)⁻¹ * (x ^ n - 1)) := by
      rw [zpow_neg, zpow_natCast, mul_sub, inv_mul_cancel₀ hxn, mul_one]
      ring
    rw [hrw, AddValuation.map_neg, AddValuation.map_mul, hinv, zero_add, hpv]
    exact val_pow_sub_one_nat v hp hp2 hv hy hn

end Formalism.MainNotions.UnusedSlot80.LTE
