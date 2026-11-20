import Mathlib

open scoped Matrix TensorProduct
open Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

open Polynomial

def logPoly {O : Type} [CommRing O] (p : ℕ) (c : ℕ → O) : O[X] :=
  ∑ k ∈ Finset.Ico 1 p, C ((-1) ^ (k - 1) * c k) * X ^ k

/- English proof (translation)
Establish `h1 : derivative (logPoly p c) = ∑ i ∈ Finset.range (p - 1), (-X : O[X]) ^ i`. Rewrite using `[logPoly, derivative_sum, Finset.sum_Ico_eq_sum_range]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi'` using `Finset.mem_range.1 hi`. Rewrite using `[derivative_C_mul_X_pow, mul_assoc, hc _ (by omega) (by omega), mul_one, show 1 + i - 1 = i by omega, neg_pow (X : O[X])]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, ← mul_neg_geom_sum, sub_neg_eq_add]`.
-/
lemma logPoly_deriv {O : Type} [CommRing O] (p : ℕ) (hp : 1 ≤ p) (c : ℕ → O)
    (hc : ∀ k, 1 ≤ k → k < p → c k * k = 1) :
    (1 + X) * derivative (logPoly p c) = 1 - (-X) ^ (p - 1) := by
  have h1 : derivative (logPoly p c) = ∑ i ∈ Finset.range (p - 1), (-X : O[X]) ^ i := by
    rw [logPoly, derivative_sum, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [derivative_C_mul_X_pow, mul_assoc, hc _ (by omega) (by omega), mul_one,
      show 1 + i - 1 = i by omega, neg_pow (X : O[X])]
    simp
  rw [h1, ← mul_neg_geom_sum, sub_neg_eq_add]

/- English proof (translation)
Use `set P := (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c with hP`. Use `set s : O[X] := (1 + X) ^ a - 1 with hs`. Establish `hXs : X ∣ s`. Use `sub_dvd_pow_sub_pow (1 + X : O[X]) 1 a` as an intermediate fact. Simplify using `using this`.

Establish `hd` using `logPoly_deriv p hp c hc`. Establish `hd2 : (1 + s) * (derivative (logPoly p c)).comp s = 1 - (-s) ^ (p - 1)`. Use `congrArg (fun q => q.comp s) hd` as an intermediate fact. Simplify using `using this`. Establish `hds : (1 + X) * derivative s = C (a : O) * (1 + s)`.

Rewrite using `[hs]`. Break down `a with _ | a` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [derivative_sub, derivative_one, sub_zero, derivative_pow_succ, derivative_add, derivative_X, zero_add, mul_one, add_sub_cancel]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hP' : (1 + X) * derivative P = C (a : O) * ((-X) ^ (p - 1) - (-s) ^ (p - 1))`. Rewrite using `[hP, derivative_sub, derivative_comp, derivative_C_mul]`. Take the linear combination `((derivative (logPoly p c)).comp s) * hds + C (a : O) * hd2 - C (a : O) * hd`. Establish `hdv : X ^ (p - 1) ∣ (1 + X) * derivative P`.

Rewrite using `[hP']`. Conclude with `Dvd.dvd.mul_left (dvd_sub (pow_dvd_pow_of_dvd (dvd_neg.2 dvd_rfl) _) (pow_dvd_pow_of_dvd (dvd_neg.2 hXs) _)) _`. Establish `hcop : IsCoprime (X ^ (p - 1) : O[X]) (1 + X)` using `IsCoprime.pow_left ⟨-1, 1, by ring⟩`. Establish `hdv2` using `X_pow_dvd_iff.1 (hcop.dvd_of_dvd_mul_left hdv)`. Use `X_pow_dvd_iff.2 fun d hdp => ?_` and prove the remaining obligations.

Break down `d with _ | d` into its components or cases. Establish `hL : X ∣ logPoly p c`. Use `Finset.dvd_sum fun k hk => Dvd.dvd.mul_left (dvd_pow_self _ ?_) _` and prove the remaining obligations. Use `(Finset.mem_Ico.1 hk).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `X_dvd_iff.1 (dvd_sub ?_ (hL.mul_left _))` and prove the remaining obligations. Take `⟨q, hq⟩` from `hL`. Rewrite using `[hq, mul_comp, X_comp]`. Conclude with `hXs.mul_right _`. Use `hdv2 d (by omega)` as an intermediate fact.

Rewrite `this` using `[coeff_derivative]`. Conclude with `(mul_eq_zero.1 this).resolve_right (by exact_mod_cast Nat.succ_ne_zero d)`.
-/
lemma logPoly_dvd {O : Type} [CommRing O] [IsDomain O] [CharZero O] (p : ℕ) (hp : 1 ≤ p)
    (c : ℕ → O) (hc : ∀ k, 1 ≤ k → k < p → c k * k = 1) (a : ℕ) :
    X ^ p ∣ (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c := by
  set P := (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c with hP
  set s : O[X] := (1 + X) ^ a - 1 with hs
  have hXs : X ∣ s := by
    have := sub_dvd_pow_sub_pow (1 + X : O[X]) 1 a
    simpa using this
  have hd := logPoly_deriv p hp c hc
  have hd2 : (1 + s) * (derivative (logPoly p c)).comp s = 1 - (-s) ^ (p - 1) := by
    have := congrArg (fun q => q.comp s) hd
    simpa using this
  have hds : (1 + X) * derivative s = C (a : O) * (1 + s) := by
    rw [hs]
    rcases a with _ | a
    · simp
    · simp only [derivative_sub, derivative_one, sub_zero, derivative_pow_succ, derivative_add,
        derivative_X, zero_add, mul_one, add_sub_cancel]
      push_cast
      ring
  have hP' : (1 + X) * derivative P = C (a : O) * ((-X) ^ (p - 1) - (-s) ^ (p - 1)) := by
    rw [hP, derivative_sub, derivative_comp, derivative_C_mul]
    linear_combination ((derivative (logPoly p c)).comp s) * hds + C (a : O) * hd2 - C (a : O) * hd
  have hdv : X ^ (p - 1) ∣ (1 + X) * derivative P := by
    rw [hP']
    exact Dvd.dvd.mul_left (dvd_sub (pow_dvd_pow_of_dvd (dvd_neg.2 dvd_rfl) _)
      (pow_dvd_pow_of_dvd (dvd_neg.2 hXs) _)) _
  have hcop : IsCoprime (X ^ (p - 1) : O[X]) (1 + X) :=
    IsCoprime.pow_left ⟨-1, 1, by ring⟩
  have hdv2 := X_pow_dvd_iff.1 (hcop.dvd_of_dvd_mul_left hdv)
  refine X_pow_dvd_iff.2 fun d hdp => ?_
  rcases d with _ | d
  · have hL : X ∣ logPoly p c := by
      refine Finset.dvd_sum fun k hk => Dvd.dvd.mul_left (dvd_pow_self _ ?_) _
      have := (Finset.mem_Ico.1 hk).1
      omega
    refine X_dvd_iff.1 (dvd_sub ?_ (hL.mul_left _))
    obtain ⟨q, hq⟩ := hL
    rw [hq, mul_comp, X_comp]
    exact hXs.mul_right _
  · have := hdv2 d (by omega)
    rw [coeff_derivative] at this
    exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast Nat.succ_ne_zero d)

section Val

variable {K : Type} [Field K] (v : Valuation K NNReal)

/- English proof (translation)
The claim follows from `(natCast_mem v.integer k : (k : K) ∈ v.integer)`.
-/
lemma val_nat_le (k : ℕ) : v (k : K) ≤ 1 := (natCast_mem v.integer k : (k : K) ∈ v.integer)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hlt : v (k : K) < 1` using `lt_of_le_of_ne (val_nat_le v k) hne`. Establish `hc : Nat.Coprime p k` using `(Nat.coprime_of_lt_prime (by omega) h2 Fact.out)`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 hc`. Establish `hab' : (a : K) * p + b * k = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → K) hab`.

Establish `ha : v (a : K) ≤ 1` using `(intCast_mem v.integer a : (a : K) ∈ v.integer)`. Establish `hb : v (b : K) ≤ 1` using `(intCast_mem v.integer b : (b : K) ∈ v.integer)`. Establish `: v ((a : K) * p + b * k) < 1`. Use `v.map_add_lt ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `mul_lt_one_of_nonneg_of_lt_one_right ha zero_le hp`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right hb zero_le hlt`. Rewrite `this` using `[hab', map_one]`. Conclude with `lt_irrefl _ this`.
-/
lemma val_nat_eq (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) (k : ℕ) (h1 : 1 ≤ k) (h2 : k < p) :
    v (k : K) = 1 := by
  by_contra hne
  have hlt : v (k : K) < 1 := lt_of_le_of_ne (val_nat_le v k) hne
  have hc : Nat.Coprime p k := (Nat.coprime_of_lt_prime (by omega) h2 Fact.out)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have hab' : (a : K) * p + b * k = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have ha : v (a : K) ≤ 1 := (intCast_mem v.integer a : (a : K) ∈ v.integer)
  have hb : v (b : K) ≤ 1 := (intCast_mem v.integer b : (b : K) ∈ v.integer)
  have : v ((a : K) * p + b * k) < 1 := by
    refine v.map_add_lt ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right ha zero_le hp
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right hb zero_le hlt
  rw [hab', map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `: v x ^ p = 1` using `by rw [← map_pow, hx, map_one]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le hp).1 this`.
-/
lemma val_root (p : ℕ) (hp : p ≠ 0) {x : K} (hx : x ^ p = 1) : v x = 1 := by
  have : v x ^ p = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hp).1 this

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `: x ^ (k + 1) - 1 = x * (x ^ k - 1) + (x - 1)` using `by ring`. Rewrite using `[this]`.

Use `v.map_add_le ?_ le_rfl` and prove the remaining obligations. Rewrite using `[map_mul, hx, one_mul]`. Conclude with `ih`.
-/
lemma val_pow_sub_one {x : K} (hx : v x = 1) (k : ℕ) : v (x ^ k - 1) ≤ v (x - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : x ^ (k + 1) - 1 = x * (x ^ k - 1) + (x - 1) := by ring
    rw [this]
    refine v.map_add_le ?_ le_rfl
    rw [map_mul, hx, one_mul]; exact ih

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Take `⟨n, rfl⟩ : ∃ n, p = n + 1` from `⟨p - 1, by have := hp.pos; omega⟩`. Establish `h` using `congrArg v hζ.prod_one_sub_pow_eq_order`. Rewrite `h` using `[map_prod]`. Use `push_cast`.

Rewrite using `[← h, Finset.prod_congr rfl (g := fun _ => v (ζ - 1))]`. Simplify using the standard rewrite rules. Introduce `k hk`. Establish `hk'` using `Finset.mem_range.1 hk`. Establish `hc : Nat.Coprime (k + 1) (n + 1)` using `(Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm`.

Establish `h2` using `hζ.pow_of_coprime _ hc`. Rewrite using `[v.map_sub_swap]`. Use `le_antisymm (val_pow_sub_one v (val_root v _ hp.ne_zero hζ.pow_eq_one) _) ?_` and prove the remaining obligations. Take `⟨i, -, hi⟩` from `h2.eq_pow_of_pow_eq_one hζ.pow_eq_one`. Use `conv_lhs => rw [← hi]`.

Conclude with `val_pow_sub_one v (val_root v _ hp.ne_zero h2.pow_eq_one) _`.
-/
lemma val_prim (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    v (ζ - 1) ^ (p - 1) = v (p : K) := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := congrArg v hζ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  push_cast
  rw [← h, Finset.prod_congr rfl (g := fun _ => v (ζ - 1))]
  · simp
  intro k hk
  have hk' := Finset.mem_range.1 hk
  have hc : Nat.Coprime (k + 1) (n + 1) :=
    (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
  have h2 := hζ.pow_of_coprime _ hc
  rw [v.map_sub_swap]
  refine le_antisymm (val_pow_sub_one v (val_root v _ hp.ne_zero hζ.pow_eq_one) _) ?_
  obtain ⟨i, -, hi⟩ := h2.eq_pow_of_pow_eq_one hζ.pow_eq_one
  conv_lhs => rw [← hi]
  exact val_pow_sub_one v (val_root v _ hp.ne_zero h2.pow_eq_one) _

def tl (p : ℕ) (x : K) : K := ∑ k ∈ Finset.Ico 1 p, (-1) ^ (k - 1) * (x - 1) ^ k / (k : K)

/- English proof (translation)
Use `Finset.sum_eq_zero fun k hk => ?_` and prove the remaining obligations. Use `(Finset.mem_Ico.1 hk).1` as an intermediate fact. Rewrite using `[sub_self, zero_pow (by omega)]; simp`.
-/
lemma tl_one (p : ℕ) : tl p (1 : K) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have := (Finset.mem_Ico.1 hk).1
  rw [sub_self, zero_pow (by omega)]; simp

/- English proof (translation)
Set `c : ℕ → v.integer` to `fun k => if h : v (k : K) = 1 then ⟨(k : K)⁻¹, by`. Rewrite using `[Valuation.mem_integer_iff, map_inv₀, h, inv_one]⟩ else 0`. Establish `hc' : ∀ k, 1 ≤ k → k < p → (c k : K) = (k : K)⁻¹`. Introduce `k h1 h2`. Simplify using `only [c, dif_pos (val_nat_eq v p hp k h1 h2)]`.

Establish `hc : ∀ k, 1 ≤ k → k < p → c k * k = 1`. Introduce `k h1 h2`. Use `ext`. Establish `: (k : K) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Use `push_cast`.

Rewrite using `[hc' k h1 h2, inv_mul_cancel₀ this]`. Establish `hev : ∀ t : v.integer, (((logPoly p c).eval t : v.integer) : K) = tl p (1 + (t : K))`. Introduce `t`. Rewrite using `[logPoly, eval_finsetSum, tl]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_Ico.1 hk`. Simplify using `only [eval_mul, eval_C, eval_pow, eval_X]`. Use `push_cast`. Rewrite using `[hc' k h1 h2, add_sub_cancel_left]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨q, hq⟩` from `logPoly_dvd p (Fact.out : p.Prime).one_le c hc a`. Establish `hx1 : x - 1 ∈ v.integer` using `sub_mem (le_of_eq hx : x ∈ v.integer) (one_mem _)`. Set `t : v.integer` to `⟨x - 1, hx1⟩`. Establish `h` using `congrArg (fun r : v.integer[X] => ((r.eval t : v.integer) : K)) hq`.

Simplify using `only [eval_sub, eval_comp, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one] at h`. Move the coercions through the operations in `at h`. Rewrite `h` using `[hev, hev]`. Move the coercions through the operations in `at h`. Establish `ht : (t : K) = x - 1` using `rfl`.

Rewrite `h` using `[ht, add_sub_cancel, add_sub_cancel, mul_comm (a : K)]`. Rewrite using `[h, map_mul, map_pow]`. Conclude with `mul_le_of_le_one_right zero_le (q.eval t).2`.
-/
lemma val_tl_pow [CharZero K] (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {x : K} (hx : v x = 1)
    (a : ℕ) : v (tl p (x ^ a) - tl p x * a) ≤ v (x - 1) ^ p := by
  classical
  let c : ℕ → v.integer := fun k => if h : v (k : K) = 1 then ⟨(k : K)⁻¹, by
    rw [Valuation.mem_integer_iff, map_inv₀, h, inv_one]⟩ else 0
  have hc' : ∀ k, 1 ≤ k → k < p → (c k : K) = (k : K)⁻¹ := by
    intro k h1 h2
    simp only [c, dif_pos (val_nat_eq v p hp k h1 h2)]
  have hc : ∀ k, 1 ≤ k → k < p → c k * k = 1 := by
    intro k h1 h2
    ext
    have : (k : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast
    rw [hc' k h1 h2, inv_mul_cancel₀ this]
  have hev : ∀ t : v.integer, (((logPoly p c).eval t : v.integer) : K) = tl p (1 + (t : K)) := by
    intro t
    rw [logPoly, eval_finsetSum, tl]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    push_cast
    rw [hc' k h1 h2, add_sub_cancel_left]; ring
  obtain ⟨q, hq⟩ := logPoly_dvd p (Fact.out : p.Prime).one_le c hc a
  have hx1 : x - 1 ∈ v.integer := sub_mem (le_of_eq hx : x ∈ v.integer) (one_mem _)
  let t : v.integer := ⟨x - 1, hx1⟩
  have h := congrArg (fun r : v.integer[X] => ((r.eval t : v.integer) : K)) hq
  simp only [eval_sub, eval_comp, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one] at h
  push_cast at h
  rw [hev, hev] at h
  push_cast at h
  have ht : (t : K) = x - 1 := rfl
  rw [ht, add_sub_cancel, add_sub_cancel, mul_comm (a : K)] at h
  rw [h, map_mul, map_pow]
  exact mul_le_of_le_one_right zero_le (q.eval t).2

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `one_le_pow₀ (n := p - 1) (not_lt.1 h)` as an intermediate fact. Rewrite `this` using `[val_prim v p hζ]`. Conclude with `absurd hp (not_lt.2 this)`.
-/
lemma val_prim_lt (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) < 1 := by
  by_contra h
  have := one_le_pow₀ (n := p - 1) (not_lt.1 h)
  rw [val_prim v p hζ] at this
  exact absurd hp (not_lt.2 this)

/- English proof (translation)
The claim follows from `(v.pos_iff).2 (sub_ne_zero.2 (hζ.ne_one (Fact.out : p.Prime).one_lt))`.
-/
lemma val_prim_pos (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : 0 < v (ζ - 1) :=
  (v.pos_iff).2 (sub_ne_zero.2 (hζ.ne_one (Fact.out : p.Prime).one_lt))

/- English proof (translation)
Rewrite using `[← val_prim v p hζ]`. Conclude with `pow_le_pow_of_le_one zero_le (val_prim_lt v p hp hζ).le (Nat.sub_le _ _)`.
-/
lemma val_prim_pow_le (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ p ≤ v (p : K) := by
  rw [← val_prim v p hζ]
  exact pow_le_pow_of_le_one zero_le (val_prim_lt v p hp hζ).le (Nat.sub_le _ _)

/- English proof (translation)
The claim follows from `pow_lt_self_of_lt_one₀ (val_prim_pos v p hζ) (val_prim_lt v p hp hζ) hk`.
-/
lemma val_prim_pow_lt (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (hk : 1 < k) : v (ζ - 1) ^ k < v (ζ - 1) :=
  pow_lt_self_of_lt_one₀ (val_prim_pos v p hζ) (val_prim_lt v p hp hζ) hk

/- English proof (translation)
Rewrite using `[tl, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : p.Prime).one_lt]`. Simplify using `only [Nat.sub_self, pow_zero, pow_one, one_mul, Nat.cast_one, div_one]`. Use `v.map_add_eq_of_lt_left (v.map_sum_lt (val_prim_pos v p hζ).ne' fun k hk => ?_)` and prove the remaining obligations. Take `⟨h1, h2⟩` from `Finset.mem_Ico.1 hk`. Rewrite using `[map_div₀, val_nat_eq v p hp k (by omega) h2, div_one, map_mul, map_pow, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]`.

Conclude with `val_prim_pow_lt v p hp hζ k (by omega)`.
-/
lemma val_tl_prim (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (tl p ζ) = v (ζ - 1) := by
  rw [tl, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : p.Prime).one_lt]
  simp only [Nat.sub_self, pow_zero, pow_one, one_mul, Nat.cast_one, div_one]
  refine v.map_add_eq_of_lt_left (v.map_sum_lt (val_prim_pos v p hζ).ne' fun k hk => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
  rw [map_div₀, val_nat_eq v p hp k (by omega) h2, div_one, map_mul, map_pow, map_pow,
    Valuation.map_neg, map_one, one_pow, one_mul]
  exact val_prim_pow_lt v p hp hζ k (by omega)

/- English proof (translation)
Establish `hpp : p.Prime` using `Fact.out`. Distinguish the cases in `h1 : x = 1`. Simplify using `[h1, tl_one]`. Establish `hζ : IsPrimitiveRoot x p`. Use `orderOf_eq_prime hx h1` as an intermediate fact.

Rewrite using `[← this]`. Conclude with `IsPrimitiveRoot.orderOf x`. Establish `: NeZero p` using `⟨hpp.ne_zero⟩`. Take `⟨b, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hy`. Establish `hv` using `val_root v p hpp.ne_zero hx`.

Establish `: tl p (x * x ^ b) - tl p x - tl p (x ^ b) = (tl p (x ^ (b + 1)) - tl p x * (b + 1 : ℕ)) - (tl p (x ^ b) - tl p x * b)`. Rewrite using `[pow_succ']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `(v.map_sub_le (val_tl_pow v p hp hv _) (val_tl_pow v p hp hv _)).trans (val_prim_pow_le v p hp hζ)`.
-/
lemma val_tl_add [CharZero K] (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {x y : K}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : v (tl p (x * y) - tl p x - tl p y) ≤ v (p : K) := by
  have hpp : p.Prime := Fact.out
  by_cases h1 : x = 1
  · simp [h1, tl_one]
  have hζ : IsPrimitiveRoot x p := by
    have := orderOf_eq_prime hx h1
    rw [← this]; exact IsPrimitiveRoot.orderOf x
  have : NeZero p := ⟨hpp.ne_zero⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
  have hv := val_root v p hpp.ne_zero hx
  have : tl p (x * x ^ b) - tl p x - tl p (x ^ b) =
      (tl p (x ^ (b + 1)) - tl p x * (b + 1 : ℕ)) - (tl p (x ^ b) - tl p x * b) := by
    rw [pow_succ']; push_cast; ring
  rw [this]
  exact (v.map_sub_le (val_tl_pow v p hp hv _) (val_tl_pow v p hp hv _)).trans
    (val_prim_pow_le v p hp hζ)

end Val

end PositivityTheory.HtPt.Ra
