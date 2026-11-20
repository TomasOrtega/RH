import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

noncomputable section

open Filter Topology

namespace GlobalTheory.PadicLogUnits

variable {l : ℕ} [hl : Fact l.Prime]

def term (y : ℚ_[l]) (k : ℕ) : ℚ_[l] := (-1 : ℚ_[l]) ^ k * y ^ (k + 1) / ((k : ℚ_[l]) + 1)

def lg (x : ℚ_[l]) : ℚ_[l] := ∑' k : ℕ, term (x - 1) k

/- English proof (translation)
Establish `h0 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Establish `h1 : ((k : ℚ_[l]) + 1) = ((k + 1 : ℕ) : ℚ_[l])` using `by push_cast; rfl`. Rewrite using `[h1, Padic.norm_eq_zpow_neg_valuation h0, Padic.valuation_natCast, zpow_neg, inv_inv, zpow_natCast]`. Establish `h2 : l ^ padicValNat l (k + 1) ≤ k + 1` using `Nat.le_of_dvd (Nat.succ_pos k) pow_padicValNat_dvd`. Establish `h3 : k + 1 ≤ 2 ^ k` using `Nat.lt_two_pow_self`.

Conclude with `h2.trans h3` after adjusting the coercions.
-/
lemma inv_norm_succ_le (k : ℕ) : ‖((k : ℚ_[l]) + 1)‖⁻¹ ≤ 2 ^ k := by
  have h0 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h1 : ((k : ℚ_[l]) + 1) = ((k + 1 : ℕ) : ℚ_[l]) := by push_cast; rfl
  rw [h1, Padic.norm_eq_zpow_neg_valuation h0, Padic.valuation_natCast, zpow_neg, inv_inv,
    zpow_natCast]
  have h2 : l ^ padicValNat l (k + 1) ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) pow_padicValNat_dvd
  have h3 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  exact_mod_cast h2.trans h3

/- English proof (translation)
Rewrite using `[norm_div, norm_pow, div_eq_mul_inv, pow_succ']`. Establish `h1 : ‖y‖ ^ k ≤ (1 / 3) ^ k` using `pow_le_pow_left₀ (norm_nonneg _) hy k`. Combine the equalities or inequalities in the displayed calculation. Conclude with `inv_norm_succ_le k`. Use `_ = ‖y‖ * (2 / 3) ^ k := by rw [mul_assoc, ← mul_pow]; norm_num`.
-/
lemma norm_pow_div_le {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) (k : ℕ) :
    ‖y ^ (k + 1) / ((k : ℚ_[l]) + 1)‖ ≤ ‖y‖ * (2 / 3) ^ k := by
  rw [norm_div, norm_pow, div_eq_mul_inv, pow_succ']
  have h1 : ‖y‖ ^ k ≤ (1 / 3) ^ k := pow_le_pow_left₀ (norm_nonneg _) hy k
  calc ‖y‖ * ‖y‖ ^ k * ‖((k : ℚ_[l]) + 1)‖⁻¹ ≤ ‖y‖ * (1 / 3) ^ k * 2 ^ k := by
        gcongr
        exact inv_norm_succ_le k
    _ = ‖y‖ * (2 / 3) ^ k := by rw [mul_assoc, ← mul_pow]; norm_num

/- English proof (translation)
Rewrite using `[term, mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Conclude with `norm_pow_div_le hy k`.
-/
lemma norm_term_le {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) (k : ℕ) :
    ‖term y k‖ ≤ ‖y‖ * (2 / 3) ^ k := by
  rw [term, mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_pow_div_le hy k

/- English proof (translation)
The claim follows from `(summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c`.
-/
lemma summable_geo (c : ℝ) : Summable fun k : ℕ => c * (2 / 3 : ℝ) ^ k :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c

/- English proof (translation)
The claim follows from `Summable.of_norm_bounded (summable_geo ‖y‖) (norm_term_le hy)`.
-/
lemma summable_term {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) : Summable (term y) :=
  Summable.of_norm_bounded (summable_geo ‖y‖) (norm_term_le hy)

/- English proof (translation)
Break down `eq_or_ne (x - 1) 0 with h | h` into its components or cases. Simplify using `[lg, h, term]`. Establish `hpos : 0 < ‖x - 1‖` using `norm_pos_iff.mpr h`. Rewrite using `[lg, (summable_term hx).tsum_eq_zero_add]`. Establish `h0 : term (x - 1) 0 = x - 1` using `by simp [term]`.

Establish `h1 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ ≤ ‖x - 1‖ * (2 / 3)`. Use `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_` and prove the remaining obligations. Use `(norm_term_le hx (k + 1)).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k)`.

Establish `h2 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ < ‖x - 1‖` using `by linarith`. Rewrite using `[h0, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne', max_eq_left h2.le]`.
-/
lemma norm_lg {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) : ‖lg x‖ = ‖x - 1‖ := by
  rcases eq_or_ne (x - 1) 0 with h | h
  · simp [lg, h, term]
  have hpos : 0 < ‖x - 1‖ := norm_pos_iff.mpr h
  rw [lg, (summable_term hx).tsum_eq_zero_add]
  have h0 : term (x - 1) 0 = x - 1 := by simp [term]
  have h1 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ ≤ ‖x - 1‖ * (2 / 3) := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    refine (norm_term_le hx (k + 1)).trans ?_
    gcongr
    exact pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k)
  have h2 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ < ‖x - 1‖ := by linarith
  rw [h0, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne', max_eq_left h2.le]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[descPochhammer_succ_eval, ih, Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma desc_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ_[l] k).eval (-1) = (-1) ^ k * (k.factorial : ℚ_[l]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast
    ring

/- English proof (translation)
The claim follows from `tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one`.
-/
lemma tendsto_pow_zero : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one

/- English proof (translation)
Establish `hk : (k.factorial : ℚ_[l]) ≠ 0` using `by exact_mod_cast k.factorial_ne_zero`. Establish `h1 : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n - 1) atTop (𝓝 (-1))`. Simplify using `using (tendsto_pow_zero (l := l)).sub_const 1`. Establish `h2` using `(((descPochhammer ℚ_[l] k).continuous.tendsto (-1)).comp h1).div_const (k.factorial : ℚ_[l])`. Rewrite `h2` using `[desc_eval_neg_one, mul_div_cancel_right₀ _ hk]`.

Use `h2.congr fun n => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_choose_eq_descPochhammer_div, Nat.cast_sub (Nat.one_le_pow _ _ hl.out.pos)]`. Simplify using the standard rewrite rules.
-/
lemma tendsto_choose (k : ℕ) :
    Tendsto (fun n : ℕ => (((l ^ n - 1).choose k : ℕ) : ℚ_[l])) atTop (𝓝 ((-1) ^ k)) := by
  have hk : (k.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h1 : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n - 1) atTop (𝓝 (-1)) := by
    simpa using (tendsto_pow_zero (l := l)).sub_const 1
  have h2 := (((descPochhammer ℚ_[l] k).continuous.tendsto (-1)).comp h1).div_const
    (k.factorial : ℚ_[l])
  rw [desc_eval_neg_one, mul_div_cancel_right₀ _ hk] at h2
  refine h2.congr fun n => ?_
  rw [Nat.cast_choose_eq_descPochhammer_div, Nat.cast_sub (Nat.one_le_pow _ _ hl.out.pos)]
  simp

/- English proof (translation)
Establish `h0 : ((M + 1 : ℕ) : ℚ_[l]) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero M`. Rewrite using `[tsum_eq_sum (s := Finset.range (M + 1)) (fun k hk => by rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]; simp)]`. Rewrite using `[add_comm 1 y, add_pow, Finset.sum_range_succ', div_eq_iff h0, Finset.sum_mul]`. Simplify using `only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Establish `hk : ((k : ℚ_[l]) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Establish `h` using `congrArg (Nat.cast : ℕ → ℚ_[l]) (Nat.add_one_mul_choose_eq M k)`. Move the coercions through the operations in `at h ⊢`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(y ^ (k + 1))) * h`.
-/
lemma pow_sub_one_div (y : ℚ_[l]) (M : ℕ) :
    ((1 + y) ^ (M + 1) - 1) / ((M + 1 : ℕ) : ℚ_[l]) =
      ∑' k : ℕ, ((M.choose k : ℕ) : ℚ_[l]) * (y ^ (k + 1) / ((k : ℚ_[l]) + 1)) := by
  have h0 : ((M + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
  rw [tsum_eq_sum (s := Finset.range (M + 1))
    (fun k hk => by rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]; simp)]
  rw [add_comm 1 y, add_pow, Finset.sum_range_succ', div_eq_iff h0, Finset.sum_mul]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((k : ℚ_[l]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h := congrArg (Nat.cast : ℕ → ℚ_[l]) (Nat.add_one_mul_choose_eq M k)
  push_cast at h ⊢
  field_simp
  linear_combination (-(y ^ (k + 1))) * h

/- English proof (translation)
Establish `h` using `tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun (n k : ℕ) => (((l ^ n - 1).choose k : ℕ) : ℚ_[l]) * ((x - 1) ^ (k + 1) / ((k : ℚ_[l]) + 1))) (g := term (x - 1)) (summable_geo ‖x - 1‖) (fun k => by`. Rewrite using `[term, mul_div_assoc]`. Conclude with `(tendsto_choose k).mul_const _)`. Use the proof step `(Eventually.of_forall fun n k => by`. Rewrite using `[norm_mul]`.

Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans (norm_pow_div_le hx k))`. Use `h.congr fun n => ?_` and prove the remaining obligations. Rewrite using `[← pow_sub_one_div, Nat.sub_add_cancel (Nat.one_le_pow _ _ hl.out.pos)]`. Simplify using the standard rewrite rules.
-/
lemma tendsto_lg {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) :
    Tendsto (fun n : ℕ => (x ^ (l ^ n) - 1) / (l : ℚ_[l]) ^ n) atTop (𝓝 (lg x)) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (n k : ℕ) => (((l ^ n - 1).choose k : ℕ) : ℚ_[l]) *
      ((x - 1) ^ (k + 1) / ((k : ℚ_[l]) + 1))) (g := term (x - 1))
    (summable_geo ‖x - 1‖) (fun k => by
      rw [term, mul_div_assoc]; exact (tendsto_choose k).mul_const _)
    (Eventually.of_forall fun n k => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
        (norm_pow_div_le hx k))
  refine h.congr fun n => ?_
  rw [← pow_sub_one_div, Nat.sub_add_cancel (Nat.one_le_pow _ _ hl.out.pos)]
  simp

/- English proof (translation)
Establish `: x * w - 1 = (x - 1) * (w - 1) + (x - 1) + (w - 1)` using `by ring`. Rewrite using `[this]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hw)` and prove the remaining obligations. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use polynomial arithmetic with `[norm_nonneg (x - 1), norm_nonneg (w - 1)]`.
-/
lemma norm_mul_sub_one {x w : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (hw : ‖w - 1‖ ≤ 1 / 3) :
    ‖x * w - 1‖ ≤ 1 / 3 := by
  have : x * w - 1 = (x - 1) * (w - 1) + (x - 1) + (w - 1) := by ring
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hw)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
  rw [norm_mul]
  nlinarith [norm_nonneg (x - 1), norm_nonneg (w - 1)]

/- English proof (translation)
Establish `h` using `((tendsto_lg hx).add (tendsto_lg hw)).add (tendsto_pow_zero.mul ((tendsto_lg hx).mul (tendsto_lg hw)))`. Rewrite `h` using `[zero_mul, add_zero]`. Use `tendsto_nhds_unique (tendsto_lg (norm_mul_sub_one hx hw)) (h.congr fun n => ?_)` and prove the remaining obligations. Establish `h0 : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast hl.out.ne_zero`. Rewrite using `[mul_pow]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma lg_mul {x w : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (hw : ‖w - 1‖ ≤ 1 / 3) :
    lg (x * w) = lg x + lg w := by
  have h := ((tendsto_lg hx).add (tendsto_lg hw)).add
    (tendsto_pow_zero.mul ((tendsto_lg hx).mul (tendsto_lg hw)))
  rw [zero_mul, add_zero] at h
  refine tendsto_nhds_unique (tendsto_lg (norm_mul_sub_one hx hw)) (h.congr fun n => ?_)
  have h0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [mul_pow]
  field_simp
  ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [lg, term]`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Use `⟨norm_mul_sub_one ih.1 hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[lg_mul ih.1 hx, ih.2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma lg_pow {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (m : ℕ) :
    ‖x ^ m - 1‖ ≤ 1 / 3 ∧ lg (x ^ m) = m * lg x := by
  induction m with
  | zero => simp [lg, term]
  | succ m ih =>
    rw [pow_succ]
    refine ⟨norm_mul_sub_one ih.1 hx, ?_⟩
    rw [lg_mul ih.1 hx, ih.2]
    push_cast
    ring

/- English proof (translation)
Use `continuousOn_tsum (fun k => ?_) (summable_geo (1 / 3)) (fun k x hx => ?_)` and prove the remaining obligations. Unfold `term fun_prop`. Use `(norm_term_le hx k).trans ?_ gcongr` and prove the remaining obligations. Conclude with `hx`.
-/
lemma continuousOn_lg : ContinuousOn (lg (l := l)) {x | ‖x - 1‖ ≤ 1 / 3} := by
  refine continuousOn_tsum (fun k => ?_) (summable_geo (1 / 3)) (fun k x hx => ?_)
  · unfold term
    fun_prop
  · refine (norm_term_le hx k).trans ?_
    gcongr
    exact hx

/- English proof (translation)
Set `z : ℤ_[l]` to `⟨u, hu.le⟩`. Establish `hz : IsUnit z` using `PadicInt.isUnit_iff.mpr hu`. Take `⟨v, hv⟩` from `hz.map (PadicInt.toZModPow (p := l) 2)`. Establish `h1` using `ZMod.pow_totient v`. Rewrite `h1` using `[Nat.totient_prime_pow hl.out (by norm_num)]`.

Establish `h2 : z ^ (l * (l - 1)) - 1 ∈ RingHom.ker (PadicInt.toZModPow (p` using `l) 2) := by`. Rewrite using `[RingHom.mem_ker, map_sub, map_pow, map_one, ← hv, ← Units.val_pow_eq_pow_val]`. Simplify using `only [Nat.add_one_sub_one, pow_one] at h1`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]`. Conclude with `h2`.
-/
lemma norm_unit_pow_sub_one {u : ℚ_[l]} (hu : ‖u‖ = 1) :
    ‖u ^ (l * (l - 1)) - 1‖ ≤ (l : ℝ) ^ (-(2 : ℕ) : ℤ) := by
  let z : ℤ_[l] := ⟨u, hu.le⟩
  have hz : IsUnit z := PadicInt.isUnit_iff.mpr hu
  obtain ⟨v, hv⟩ := hz.map (PadicInt.toZModPow (p := l) 2)
  have h1 := ZMod.pow_totient v
  rw [Nat.totient_prime_pow hl.out (by norm_num)] at h1
  have h2 : z ^ (l * (l - 1)) - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) 2) := by
    rw [RingHom.mem_ker, map_sub, map_pow, map_one, ← hv, ← Units.val_pow_eq_pow_val]
    simp only [Nat.add_one_sub_one, pow_one] at h1
    rw [h1]
    simp
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at h2
  exact h2

/- English proof (translation)
Establish `h3 : 3 ≤ l ^ j`. Distinguish the cases in `h : l = 2`. Substitute `h` using the available equality. Conclude with `le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (h2 rfl))`. Use `hl.out.two_le` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zpow_neg, zpow_natCast, one_div]`. Conclude with `inv_anti₀ (by norm_num) (by exact_mod_cast h3)`.
-/
lemma zpow_le_third {j : ℕ} (h1 : 1 ≤ j) (h2 : l = 2 → 2 ≤ j) :
    (l : ℝ) ^ (-(j : ℤ)) ≤ 1 / 3 := by
  have h3 : 3 ≤ l ^ j := by
    by_cases h : l = 2
    · subst h
      exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (h2 rfl))
    · have := hl.out.two_le
      calc 3 ≤ l ^ 1 := by rw [pow_one]; omega
        _ ≤ l ^ j := Nat.pow_le_pow_right hl.out.pos h1
  rw [zpow_neg, zpow_natCast, one_div]
  exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)

/- English proof (translation)
The claim follows from `(norm_unit_pow_sub_one hu).trans (zpow_le_third (by norm_num) fun _ => le_rfl)`.
-/
lemma norm_unit_pow_sub_one' {u : ℚ_[l]} (hu : ‖u‖ = 1) : ‖u ^ (l * (l - 1)) - 1‖ ≤ 1 / 3 :=
  (norm_unit_pow_sub_one hu).trans (zpow_le_third (by norm_num) fun _ => le_rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma logZl_eq (u : ℚ_[l]) :
    Formalism.MainNotions.LocalSituation.logZl l u = lg (u ^ (l * (l - 1))) / ((l : ℚ_[l]) * ((l : ℚ_[l]) - 1)) := rfl

/- English proof (translation)
Establish `h : ‖(l : ℚ_[l])‖ < ‖(-1 : ℚ_[l])‖`. Simplify using `using Padic.norm_p_lt_one (p := l)`. Rewrite using `[sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le]`. Simplify using the standard rewrite rules.
-/
lemma norm_sub_one : ‖(l : ℚ_[l]) - 1‖ = 1 := by
  have h : ‖(l : ℚ_[l])‖ < ‖(-1 : ℚ_[l])‖ := by
    simpa using Padic.norm_p_lt_one (p := l)
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le]
  simp

/- English proof (translation)
Introduce `l hl`. Use `⟨fun u w hu hw => ?_, ?_, fun u hu => ?_, fun j h1 h2 u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[logZl_eq, logZl_eq, logZl_eq, mul_pow, lg_mul (norm_unit_pow_sub_one' hu) (norm_unit_pow_sub_one' hw), add_div]`. Conclude with `(continuousOn_lg.comp (continuous_pow (l * (l - 1))).continuousOn fun u hu => norm_unit_pow_sub_one' hu).div_const _`. Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast hl.out.one_le`.

Rewrite using `[logZl_eq, norm_div, norm_lg (norm_unit_pow_sub_one' hu), norm_mul, norm_sub_one, mul_one, Padic.norm_p, div_le_one (by positivity)]`. Use `(norm_unit_pow_sub_one hu).trans ?_` and prove the remaining obligations. Rewrite using `[← zpow_neg_one]`. Conclude with `zpow_le_zpow_right₀ hl1 (by norm_num)`. Establish `hu'` using `hu.trans (zpow_le_third h1 h2)`.

Establish `h0 : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast hl.out.ne_zero`. Establish `h3 : (l : ℚ_[l]) - 1 ≠ 0`. Rewrite using `[← norm_ne_zero_iff, norm_sub_one]`. Conclude with `one_ne_zero`. Rewrite using `[logZl_eq, (lg_pow hu' _).2, Nat.cast_mul, Nat.cast_sub hl.out.one_le, Nat.cast_one, mul_div_cancel_left₀ _ (mul_ne_zero h0 h3), norm_lg hu']`.
-/
theorem logZl_hom : ∀ (l : ℕ) [Fact l.Prime],
    (∀ u w : ℚ_[l], ‖u‖ = 1 → ‖w‖ = 1 →
      Formalism.MainNotions.LocalSituation.logZl l (u * w) = Formalism.MainNotions.LocalSituation.logZl l u + Formalism.MainNotions.LocalSituation.logZl l w) ∧
    ContinuousOn (Formalism.MainNotions.LocalSituation.logZl l) {u | ‖u‖ = 1} ∧
    (∀ u : ℚ_[l], ‖u‖ = 1 → ‖Formalism.MainNotions.LocalSituation.logZl l u‖ ≤ 1) ∧
    ∀ j : ℕ, 1 ≤ j → (l = 2 → 2 ≤ j) → ∀ u : ℚ_[l], ‖u - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ)) →
      ‖Formalism.MainNotions.LocalSituation.logZl l u‖ = ‖u - 1‖ := by
  intro l hl
  refine ⟨fun u w hu hw => ?_, ?_, fun u hu => ?_, fun j h1 h2 u hu => ?_⟩
  · rw [logZl_eq, logZl_eq, logZl_eq, mul_pow,
      lg_mul (norm_unit_pow_sub_one' hu) (norm_unit_pow_sub_one' hw), add_div]
  · exact (continuousOn_lg.comp (continuous_pow (l * (l - 1))).continuousOn
      fun u hu => norm_unit_pow_sub_one' hu).div_const _
  · have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_le
    rw [logZl_eq, norm_div, norm_lg (norm_unit_pow_sub_one' hu), norm_mul, norm_sub_one,
      mul_one, Padic.norm_p, div_le_one (by positivity)]
    refine (norm_unit_pow_sub_one hu).trans ?_
    rw [← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1 (by norm_num)
  · have hu' := hu.trans (zpow_le_third h1 h2)
    have h0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    have h3 : (l : ℚ_[l]) - 1 ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_sub_one]; exact one_ne_zero
    rw [logZl_eq, (lg_pow hu' _).2, Nat.cast_mul, Nat.cast_sub hl.out.one_le, Nat.cast_one,
      mul_div_cancel_left₀ _ (mul_ne_zero h0 h3), norm_lg hu']

end GlobalTheory.PadicLogUnits
