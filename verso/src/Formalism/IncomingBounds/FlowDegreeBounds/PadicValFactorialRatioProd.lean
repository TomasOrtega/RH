import Formalism.IncomingBounds.LevelTail

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

/- English proof (translation)
Introduce `l hl`. Establish `hlR : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (l : ℝ) ≠ 0` using `by positivity`. Establish `hA : 0 < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hB : 0 < (l : ℝ) - 1` using `by linarith`.

Establish `hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1` using `mul_one_div_cancel hA.ne'`. Establish `hr : ((l : ℝ) - 1) * (1 / ((l : ℝ) - 1)) = 1` using `mul_one_div_cancel hB.ne'`. Establish `hl1 : (l : ℝ) * (l : ℝ)⁻¹ = 1` using `mul_inv_cancel₀ hl0`. Establish `hl2 : (l : ℝ) ^ 2 * ((l : ℝ) ^ 2)⁻¹ = 1` using `mul_inv_cancel₀ (pow_ne_zero 2 hl0)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hu0 : (0 : ℝ) ≤ ((l : ℝ) ^ 2)⁻¹` using `by positivity`. Establish `hu1 : ((l : ℝ) ^ 2)⁻¹ < 1`. Use polynomial arithmetic with `[mul_nonneg (by nlinarith : (0 : ℝ) ≤ (l : ℝ) ^ 2 - 4) hu0]`. Establish `hg` using `(hasSum_geometric_of_lt_one hu0 hu1).mul_left ((l : ℝ)⁻¹)`. Establish `hf : (fun k : ℕ => ((l : ℝ) ^ (2 * k + 1))⁻¹) = fun k : ℕ => (l : ℝ)⁻¹ * ((l : ℝ) ^ 2)⁻¹ ^ k`.

Use function extensionality and compare the values at `k`. Rewrite using `[pow_succ, pow_mul, mul_inv, ← inv_pow, mul_comm]`. Establish `hu : (1 : ℝ) - ((l : ℝ) ^ 2)⁻¹ = ((l : ℝ) ^ 2 - 1) * ((l : ℝ) ^ 2)⁻¹`. Take the linear combination `(-1 : ℝ) * hl2`. Establish `hv : gam l = (l : ℝ)⁻¹ * (1 - ((l : ℝ) ^ 2)⁻¹)⁻¹`.

Rewrite using `[gam, hu, mul_inv, inv_inv]`. Take the linear combination `(-((l : ℝ) * ((l : ℝ) ^ 2 - 1)⁻¹)) * hl1`. Rewrite using `[hf, hv]`. Conclude with `hg`. Unfold `rho gam`.

Take the linear combination `(1 / ((l : ℝ) - 1)) * hq - ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr`.
-/
theorem constantIdentities : Constants := by
  intro l hl
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hA : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hB : 0 < (l : ℝ) - 1 := by linarith
  have hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 := mul_one_div_cancel hA.ne'
  have hr : ((l : ℝ) - 1) * (1 / ((l : ℝ) - 1)) = 1 := mul_one_div_cancel hB.ne'
  have hl1 : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hl2 : (l : ℝ) ^ 2 * ((l : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hl0)
  refine ⟨?_, ?_⟩
  · have hu0 : (0 : ℝ) ≤ ((l : ℝ) ^ 2)⁻¹ := by positivity
    have hu1 : ((l : ℝ) ^ 2)⁻¹ < 1 := by
      nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ (l : ℝ) ^ 2 - 4) hu0]
    have hg := (hasSum_geometric_of_lt_one hu0 hu1).mul_left ((l : ℝ)⁻¹)
    have hf : (fun k : ℕ => ((l : ℝ) ^ (2 * k + 1))⁻¹) = fun k : ℕ => (l : ℝ)⁻¹ * ((l : ℝ) ^ 2)⁻¹ ^ k := by
      funext k
      rw [pow_succ, pow_mul, mul_inv, ← inv_pow, mul_comm]
    have hu : (1 : ℝ) - ((l : ℝ) ^ 2)⁻¹ = ((l : ℝ) ^ 2 - 1) * ((l : ℝ) ^ 2)⁻¹ := by
      linear_combination (-1 : ℝ) * hl2
    have hv : gam l = (l : ℝ)⁻¹ * (1 - ((l : ℝ) ^ 2)⁻¹)⁻¹ := by
      rw [gam, hu, mul_inv, inv_inv]
      linear_combination (-((l : ℝ) * ((l : ℝ) ^ 2 - 1)⁻¹)) * hl1
    rw [hf, hv]
    exact hg
  · unfold rho gam
    linear_combination (1 / ((l : ℝ) - 1)) * hq - ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Use `push_cast`.

Use polynomial arithmetic with `[mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg hx hx), mul_le_mul_of_nonneg_right ih (by linarith : (0:ℝ) ≤ 1 + x)]`.
-/
private theorem one_add_mul_le_one_add_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : 1 + k * x ≤ (1 + x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg hx hx),
      mul_le_mul_of_nonneg_right ih (by linarith : (0:ℝ) ≤ 1 + x)]

/- English proof (translation)
Introduce `l hl`. Establish `hlR : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.two_le`. Establish `hB : 0 < (l : ℝ) - 1` using `by linarith`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `n hn`.

Establish `hle : l ^ padicValNat l n ≤ n` using `Nat.le_of_dvd (by omega) pow_padicValNat_dvd`. Establish `hleR : (l : ℝ) ^ padicValNat l n ≤ n` using `by exact_mod_cast hle`. Establish `hb` using `one_add_mul_le_one_add_pow ((l : ℝ) - 1) hB.le (padicValNat l n)`. Rewrite `hb` using `[show (1 : ℝ) + ((l : ℝ) - 1) = l by ring]`. Rewrite using `[le_sub_iff_add_le, div_add' _ _ _ hB.ne', div_le_div_iff_of_pos_right hB]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `e`. Unfold `rho`. Establish `hA : 0 < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1` using `mul_one_div_cancel hA.ne'`.

Establish `hb` using `one_add_mul_le_one_add_pow ((l : ℝ) ^ 2 - 1) hA.le e`. Rewrite `hb` using `[show (1 : ℝ) + ((l : ℝ) ^ 2 - 1) = (l : ℝ) ^ 2 by ring]`. Establish `hm` using `mul_le_mul_of_nonneg_right hb (one_div_pos.2 hA).le`. Establish `he : (1 + (e : ℝ) * ((l : ℝ) ^ 2 - 1)) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 / ((l : ℝ) ^ 2 - 1) + e`. Take the linear combination `(e : ℝ) * hq`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem padicValuationGain : ValGain := by
  intro l hl
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hB : 0 < (l : ℝ) - 1 := by linarith
  refine ⟨?_, ?_⟩
  · intro n hn
    have hle : l ^ padicValNat l n ≤ n := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hleR : (l : ℝ) ^ padicValNat l n ≤ n := by exact_mod_cast hle
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) - 1) hB.le (padicValNat l n)
    rw [show (1 : ℝ) + ((l : ℝ) - 1) = l by ring] at hb
    rw [le_sub_iff_add_le, div_add' _ _ _ hB.ne', div_le_div_iff_of_pos_right hB]
    linarith
  · intro e
    unfold rho
    have hA : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
    have hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 := mul_one_div_cancel hA.ne'
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) ^ 2 - 1) hA.le e
    rw [show (1 : ℝ) + ((l : ℝ) ^ 2 - 1) = (l : ℝ) ^ 2 by ring] at hb
    have hm := mul_le_mul_of_nonneg_right hb (one_div_pos.2 hA).le
    have he : (1 + (e : ℝ) * ((l : ℝ) ^ 2 - 1)) * (1 / ((l : ℝ) ^ 2 - 1)) =
        1 / ((l : ℝ) ^ 2 - 1) + e := by
      linear_combination (e : ℝ) * hq
    linarith

/- English proof (translation)
Introduce `l hl i hi`. Unfold `rho gam`. Establish `hlR : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (l : ℝ) ≠ 0` using `by positivity`. Establish `hA : 0 < (l : ℝ) ^ 2 - 1` using `by nlinarith`.

Establish `hB : 0 < (l : ℝ) - 1` using `by linarith`. Establish `hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1` using `mul_one_div_cancel hA.ne'`. Establish `hr : ((l : ℝ) - 1) * (1 / ((l : ℝ) - 1)) = 1` using `mul_one_div_cancel hB.ne'`. Establish `hP : (l : ℝ) ^ i * ((l : ℝ) ^ i)⁻¹ = 1` using `mul_inv_cancel₀ (pow_ne_zero i hl0)`. Establish `hPL : (l : ℝ) ≤ (l : ℝ) ^ i`.

Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Rewrite using `[pow_succ]`. Establish `hb` using `one_add_mul_le_one_add_pow ((l : ℝ) - 1) hB.le j`. Rewrite `hb` using `[show (1 : ℝ) + ((l : ℝ) - 1) = l by ring]`. Establish `hj : (1 : ℝ) ≤ (l : ℝ) ^ j`.

Use polynomial arithmetic with `[mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hB.le]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take the linear combination `(1 / 2 : ℝ) * hP - ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr + (1 / ((l : ℝ) - 1)) * hq`. Introduce `B`.

Take the linear combination `(B / 2) * hP - B * ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr + B * (1 / ((l : ℝ) - 1)) * hq`. Take the linear combination `(l : ℝ) ^ i * ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr - (l : ℝ) ^ i * (1 / ((l : ℝ) - 1)) * hq`. Establish `e : ((l : ℝ) ^ i + 1) * ((l : ℝ) / ((l : ℝ) ^ 2 - 1)) - 1 = (((l : ℝ) ^ i + 1) * l - ((l : ℝ) ^ 2 - 1)) * (1 / ((l : ℝ) ^ 2 - 1))`. Take the linear combination `hq`. Rewrite using `[e]`.

Use `mul_nonneg ?_ (one_div_pos.2 hA).le` and prove the remaining obligations. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hPL (by linarith : (0 : ℝ) ≤ l)]`.
-/
theorem weight_identities' : WeightIdentities := by
  intro l hl i hi
  unfold rho gam
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hA : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hB : 0 < (l : ℝ) - 1 := by linarith
  have hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 := mul_one_div_cancel hA.ne'
  have hr : ((l : ℝ) - 1) * (1 / ((l : ℝ) - 1)) = 1 := mul_one_div_cancel hB.ne'
  have hP : (l : ℝ) ^ i * ((l : ℝ) ^ i)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero i hl0)
  have hPL : (l : ℝ) ≤ (l : ℝ) ^ i := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [pow_succ]
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) - 1) hB.le j
    rw [show (1 : ℝ) + ((l : ℝ) - 1) = l by ring] at hb
    have hj : (1 : ℝ) ≤ (l : ℝ) ^ j := by
      nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hB.le]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℝ) * hP - ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr +
      (1 / ((l : ℝ) - 1)) * hq
  · intro B
    linear_combination (B / 2) * hP - B * ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr +
      B * (1 / ((l : ℝ) - 1)) * hq
  · linear_combination (l : ℝ) ^ i * ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr -
      (l : ℝ) ^ i * (1 / ((l : ℝ) - 1)) * hq
  · have e : ((l : ℝ) ^ i + 1) * ((l : ℝ) / ((l : ℝ) ^ 2 - 1)) - 1 =
        (((l : ℝ) ^ i + 1) * l - ((l : ℝ) ^ 2 - 1)) * (1 / ((l : ℝ) ^ 2 - 1)) := by
      linear_combination hq
    rw [e]
    refine mul_nonneg ?_ (one_div_pos.2 hA).le
    nlinarith [mul_le_mul_of_nonneg_right hPL (by linarith : (0 : ℝ) ≤ l)]

/- English proof (translation)
Introduce `l hl i x`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Rewrite using `[Finset.sum_range_succ, Finset.prod_range_succ]`.

Establish `hl0 : (l : ℚ) ≠ 0`. Establish `: (0 : ℚ) < l` using `by exact_mod_cast (show 0 < l by omega)`. Conclude with `this.ne'`. Establish `hne : (l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ) ≠ 0` using `mul_ne_zero (pow_ne_zero _ hl0) (by exact_mod_cast Nat.factorial_ne_zero _)`. Establish `hsq : ((-1 : ℚ) ^ (l ^ i * x)) * ((-1 : ℚ) ^ (l ^ i * x)) = 1`.

Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Establish `key : (((l ^ (i + 1) * x).factorial : ℕ) : ℚ) = (-1) ^ (l ^ i * x) * (l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ) * uFac l (l ^ i * x)`. Unfold `uFac`. Establish `h1 : l ^ (i + 1) * x = l * (l ^ i * x)` using `by ring`.

Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsq, div_self hne]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by ring`.

Rewrite using `[key, ih, add_mul, pow_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factorialSplit : FactSplit := by
  intro l hl i x
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hl0 : (l : ℚ) ≠ 0 := by
      have : (0 : ℚ) < l := by exact_mod_cast (show 0 < l by omega)
      exact this.ne'
    have hne : (l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hl0) (by exact_mod_cast Nat.factorial_ne_zero _)
    have hsq : ((-1 : ℚ) ^ (l ^ i * x)) * ((-1 : ℚ) ^ (l ^ i * x)) = 1 := by
      rw [← mul_pow]; norm_num
    have key : (((l ^ (i + 1) * x).factorial : ℕ) : ℚ) =
        (-1) ^ (l ^ i * x) * (l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ) *
          uFac l (l ^ i * x) := by
      unfold uFac
      have h1 : l ^ (i + 1) * x = l * (l ^ i * x) := by ring
      rw [h1]
      calc (((l * (l ^ i * x)).factorial : ℕ) : ℚ)
          = ((-1 : ℚ) ^ (l ^ i * x) * (-1) ^ (l ^ i * x)) * ((l * (l ^ i * x)).factorial : ℚ) *
              (((l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ)) /
                ((l : ℚ) ^ (l ^ i * x) * ((l ^ i * x).factorial : ℚ))) := by
            rw [hsq, div_self hne]; ring
        _ = _ := by ring
    rw [key, ih, add_mul, pow_add, pow_add]
    ring

/- English proof (translation)
Use `Fact.mk hl` as an intermediate fact. Establish `h` using `sub_one_mul_padicValNat_factorial (p := l) m`. Establish `hs` using `Nat.digit_sum_le l m`. Establish `h1 : 1 ≤ l` using `hl.one_lt.le`. Establish `h' : (((l - 1) * padicValNat l m.factorial : ℕ) : ℝ) = ((m - (l.digits m).sum : ℕ) : ℝ)`.

Rewrite using `[h]`. Move the coercions through the operations in `[Nat.cast_sub h1, Nat.cast_sub hs] at h'`. Simplify `h'` using `[Nat.cast_list_sum]`.
-/
private theorem sub_one_mul_padicValNat_factorial_eq (l m : ℕ) (hl : l.Prime) :
    ((l : ℝ) - 1) * (padicValNat l m.factorial : ℝ) = (m : ℝ) - ((l.digits m).sum : ℝ) := by
  have := Fact.mk hl
  have h := sub_one_mul_padicValNat_factorial (p := l) m
  have hs := Nat.digit_sum_le l m
  have h1 : 1 ≤ l := hl.one_lt.le
  have h' : (((l - 1) * padicValNat l m.factorial : ℕ) : ℝ) = ((m - (l.digits m).sum : ℕ) : ℝ) := by
    rw [h]
  push_cast [Nat.cast_sub h1, Nat.cast_sub hs] at h'
  simpa [Nat.cast_list_sum] using h'

/- English proof (translation)
Establish `hlR : (2 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hn : (1 : ℝ) ≤ n` using `by exact_mod_cast (show 1 ≤ n by omega)`. Establish `hlog0 : 0 ≤ Real.logb l n` using `Real.logb_nonneg (by linarith) hn`. Break down `Nat.eq_zero_or_pos a with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Simplify using `only [Nat.digits_zero, List.sum_nil, Nat.cast_zero]`. Conclude with `mul_nonneg (by linarith) (by linarith)`. Establish `hlen : (l.digits a).length = Nat.log l a + 1` using `Nat.digits_len l a (by omega) (by omega)`. Establish `hsum : (l.digits a).sum ≤ (l.digits a).length • (l - 1)` using `List.sum_le_card_nsmul (l.digits a) (l - 1) (fun x hx => by`. Use `Nat.digits_lt_base (by omega) hx` as an intermediate fact.

Use the proof step `omega)`. Rewrite `hsum` using `[hlen, smul_eq_mul]`. Establish `hsumR : ((l.digits a).sum : ℝ) ≤ ((Nat.log l a : ℝ) + 1) * ((l : ℝ) - 1)`. Establish `h' : (((l.digits a).sum : ℕ) : ℝ) ≤ (((Nat.log l a + 1) * (l - 1) : ℕ) : ℝ)`. Conclude with `hsum` after adjusting the coercions.

Move the coercions through the operations in `[Nat.cast_sub (show 1 ≤ l by omega)] at h'`. Simplify `h'` using `[Nat.cast_list_sum]`. Establish `hlog : (Nat.log l a : ℝ) ≤ Real.logb l n`. Establish `hpow : l ^ Nat.log l a ≤ a` using `Nat.pow_log_le_self l (by omega)`. Rewrite using `[Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_natCast]`.

Conclude with `hpow.trans ha.le` after adjusting the coercions. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hlog (by linarith : (0:ℝ) ≤ (l : ℝ) - 1)]`.
-/
private theorem digits_sum_le_sub_one_mul_logb_add_one (l a : ℕ) (hl : 2 ≤ l) (n : ℕ) (ha : a < n) :
    ((l.digits a).sum : ℝ) ≤ ((l : ℝ) - 1) * (Real.logb l n + 1) := by
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog0 : 0 ≤ Real.logb l n := Real.logb_nonneg (by linarith) hn
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0
    simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero]
    exact mul_nonneg (by linarith) (by linarith)
  · have hlen : (l.digits a).length = Nat.log l a + 1 := Nat.digits_len l a (by omega) (by omega)
    have hsum : (l.digits a).sum ≤ (l.digits a).length • (l - 1) :=
      List.sum_le_card_nsmul (l.digits a) (l - 1) (fun x hx => by
        have := Nat.digits_lt_base (by omega) hx
        omega)
    rw [hlen, smul_eq_mul] at hsum
    have hsumR : ((l.digits a).sum : ℝ) ≤ ((Nat.log l a : ℝ) + 1) * ((l : ℝ) - 1) := by
      have h' : (((l.digits a).sum : ℕ) : ℝ) ≤ (((Nat.log l a + 1) * (l - 1) : ℕ) : ℝ) := by
        exact_mod_cast hsum
      push_cast [Nat.cast_sub (show 1 ≤ l by omega)] at h'
      simpa [Nat.cast_list_sum] using h'
    have hlog : (Nat.log l a : ℝ) ≤ Real.logb l n := by
      have hpow : l ^ Nat.log l a ≤ a := Nat.pow_log_le_self l (by omega)
      rw [Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_natCast]
      exact_mod_cast hpow.trans ha.le
    nlinarith [mul_le_mul_of_nonneg_right hlog (by linarith : (0:ℝ) ≤ (l : ℝ) - 1)]

/- English proof (translation)
Use `Fact.mk hl` as an intermediate fact. Establish `hdvd : a.factorial ∣ (y + a).factorial` using `Nat.factorial_dvd_factorial (by omega)`. Establish `hq0 : (y + a).factorial / a.factorial ≠ 0` using `(Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos a)).ne'`. Establish `hsplit : (y + a).factorial = a.factorial * ((y + a).factorial / a.factorial)` using `(Nat.mul_div_cancel' hdvd).symm`. Establish `hv : padicValNat l (y + a).factorial = padicValNat l a.factorial + padicValNat l ((y + a).factorial / a.factorial)`.

Rewrite using `[← padicValNat.mul (Nat.factorial_ne_zero a) hq0, ← hsplit]`. Establish `hv' : (padicValNat l (y + a).factorial : ℝ) = (padicValNat l a.factorial : ℝ) + (padicValNat l ((y + a).factorial / a.factorial) : ℝ)`. Conclude with `hv` after adjusting the coercions. Establish `e1` using `sub_one_mul_padicValNat_factorial_eq l (y + a) hl`. Establish `e2` using `sub_one_mul_padicValNat_factorial_eq l a hl`.

Rewrite `e1` using `[hv', Nat.cast_add]`. Establish `hs` using `digits_sum_le_sub_one_mul_logb_add_one l a hl.two_le n ha`. Establish `hs0 : (0 : ℝ) ≤ ((l.digits (y + a)).sum : ℝ)` using `Nat.cast_nonneg _`. Establish `hlR : (2 : ℝ) ≤ l` using `by exact_mod_cast hl.two_le`. Establish `hlpos : 0 < (l : ℝ) - 1` using `by linarith`.

Establish `key : ((l : ℝ) - 1) * (padicValNat l ((y + a).factorial / a.factorial) : ℝ) ≤ (y : ℝ) + ((l : ℝ) - 1) * (Real.logb l n + 1)`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[div_add' _ _ _ hlpos.ne', le_div_iff₀ hlpos]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem padicValNat_factorial_div_factorial_le (l : ℕ) (hl : l.Prime) (y a n : ℕ) (ha : a < n) :
    (padicValNat l ((y + a).factorial / a.factorial) : ℝ) ≤
      (y : ℝ) / ((l : ℝ) - 1) + (Real.logb l n + 1) := by
  have := Fact.mk hl
  have hdvd : a.factorial ∣ (y + a).factorial := Nat.factorial_dvd_factorial (by omega)
  have hq0 : (y + a).factorial / a.factorial ≠ 0 :=
    (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos a)).ne'
  have hsplit : (y + a).factorial = a.factorial * ((y + a).factorial / a.factorial) :=
    (Nat.mul_div_cancel' hdvd).symm
  have hv : padicValNat l (y + a).factorial =
      padicValNat l a.factorial + padicValNat l ((y + a).factorial / a.factorial) := by
    rw [← padicValNat.mul (Nat.factorial_ne_zero a) hq0, ← hsplit]
  have hv' : (padicValNat l (y + a).factorial : ℝ) =
      (padicValNat l a.factorial : ℝ) + (padicValNat l ((y + a).factorial / a.factorial) : ℝ) := by
    exact_mod_cast hv
  have e1 := sub_one_mul_padicValNat_factorial_eq l (y + a) hl
  have e2 := sub_one_mul_padicValNat_factorial_eq l a hl
  rw [hv', Nat.cast_add] at e1
  have hs := digits_sum_le_sub_one_mul_logb_add_one l a hl.two_le n ha
  have hs0 : (0 : ℝ) ≤ ((l.digits (y + a)).sum : ℝ) := Nat.cast_nonneg _
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hlpos : 0 < (l : ℝ) - 1 := by linarith
  have key : ((l : ℝ) - 1) * (padicValNat l ((y + a).factorial / a.factorial) : ℝ) ≤
      (y : ℝ) + ((l : ℝ) - 1) * (Real.logb l n + 1) := by
    nlinarith
  rw [div_add' _ _ _ hlpos.ne', le_div_iff₀ hlpos]
  nlinarith

/- English proof (translation)
Introduce `l hl n0 n y hn0`. Use `Fact.mk hl` as an intermediate fact. Establish `hprod : ∀ m, m ≤ n → (padicValNat l (capNat m y) : ℝ) ≤ (m : ℝ) * y / ((l : ℝ) - 1) + m * (Real.logb l n + 1)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro _`. Simplify using `[capNat]`. Consider the case `succ m ih`. Introduce `hm`. Establish `hne1 : capNat m y ≠ 0`.

Unfold `capNat`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `a _`. Conclude with `(Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos a)).ne'`. Establish `hne2 : (y + m).factorial / m.factorial ≠ 0` using `(Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos m)).ne'`.

Establish `hsplit : capNat (m + 1) y = capNat m y * ((y + m).factorial / m.factorial)`. Unfold `capNat`. Rewrite using `[Finset.prod_range_succ]`. Rewrite using `[hsplit, padicValNat.mul hne1 hne2]`. Use `push_cast`.

Establish `h1` using `ih (by omega)`. Establish `h2` using `padicValNat_factorial_div_factorial_le l hl y m n (by omega)`. Establish `e : ((m : ℝ) + 1) * y / ((l : ℝ) - 1) = (m : ℝ) * y / ((l : ℝ) - 1) + y / ((l : ℝ) - 1)`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h` using `hprod n0 hn0`. Establish `hL : 0 ≤ Real.logb l n + 1`. Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Simplify using the standard rewrite rules.

Establish `h1 : (1 : ℝ) ≤ n` using `by exact_mod_cast h0`. Use `Real.logb_nonneg (b := (l : ℝ)) (by exact_mod_cast hl.one_lt) h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0R : (n0 : ℝ) ≤ n` using `by exact_mod_cast hn0`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hn0R hL]`.
-/
theorem padicValFactorialRatioProd : CapVal := by
  intro l hl n0 n y hn0
  have := Fact.mk hl
  have hprod : ∀ m, m ≤ n → (padicValNat l (capNat m y) : ℝ) ≤
      (m : ℝ) * y / ((l : ℝ) - 1) + m * (Real.logb l n + 1) := by
    intro m
    induction m with
    | zero => intro _; simp [capNat]
    | succ m ih =>
      intro hm
      have hne1 : capNat m y ≠ 0 := by
        unfold capNat
        rw [Finset.prod_ne_zero_iff]
        intro a _
        exact (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos a)).ne'
      have hne2 : (y + m).factorial / m.factorial ≠ 0 :=
        (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos m)).ne'
      have hsplit : capNat (m + 1) y =
          capNat m y * ((y + m).factorial / m.factorial) := by
        unfold capNat
        rw [Finset.prod_range_succ]
      rw [hsplit, padicValNat.mul hne1 hne2]
      push_cast
      have h1 := ih (by omega)
      have h2 := padicValNat_factorial_div_factorial_le l hl y m n (by omega)
      have e : ((m : ℝ) + 1) * y / ((l : ℝ) - 1) = (m : ℝ) * y / ((l : ℝ) - 1) + y / ((l : ℝ) - 1) := by
        ring
      linarith
  have h := hprod n0 hn0
  have hL : 0 ≤ Real.logb l n + 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
      have := Real.logb_nonneg (b := (l : ℝ)) (by exact_mod_cast hl.one_lt) h1
      linarith
  have hn0R : (n0 : ℝ) ≤ n := by exact_mod_cast hn0
  nlinarith [mul_le_mul_of_nonneg_right hn0R hL]

end Formalism.IncomingBounds
