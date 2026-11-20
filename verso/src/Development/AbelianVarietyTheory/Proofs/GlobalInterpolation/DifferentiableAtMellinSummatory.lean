import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LGrowth

open Filter Topology Asymptotics

/- English proof (translation)
Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Establish `hper : ∀ m : ℕ, ∑ k ∈ Finset.range q, χ ((m + k : ℕ) : ZMod q) = 0`. Introduce `m`. Establish `h0 : ∑ a : ZMod q, χ a = 0` using `χ.sum_eq_zero_of_ne_one hχ`. Rewrite using `[← h0, ← Equiv.sum_comp (Equiv.addLeft (m : ZMod q))]`.

Use `Finset.sum_bij (fun k _ => (k : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb hab`. Use `(ZMod.natCast_eq_natCast_iff' a b q).1 hab` as an intermediate fact. Rewrite `this` using `[Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]`. Then use the resulting hypothesis. Introduce `b _`.

Conclude with `⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩`. Introduce `a _`. Simplify using the standard rewrite rules. Establish `hI : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q) = ∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q)`. Introduce `n`.

Rewrite using `[← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]`. Simplify using the standard rewrite rules. Rewrite using `[hI]`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Break down `lt_or_ge n q with h | h` into its components or cases. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_sum fun k _ => χ.norm_le_one _).trans ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Conclude with `h.le` after adjusting the coercions.

Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le' h`. Rewrite using `[Finset.sum_range_add]`. Use `hper (1 + m)` as an intermediate fact. Simplify using `only [← add_assoc]`. Rewrite using `[this, add_zero]`.

Conclude with `ih m (by omega)`.
-/
theorem norm_partialSum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hper : ∀ m : ℕ, ∑ k ∈ Finset.range q, χ ((m + k : ℕ) : ZMod q) = 0 := by
    intro m
    have h0 : ∑ a : ZMod q, χ a = 0 := χ.sum_eq_zero_of_ne_one hχ
    rw [← h0, ← Equiv.sum_comp (Equiv.addLeft (m : ZMod q))]
    refine Finset.sum_bij (fun k _ => (k : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      have := (ZMod.natCast_eq_natCast_iff' a b q).1 hab
      rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
        at this
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
    · intro a _
      simp
  have hI : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)
      = ∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q) := by
    intro n
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp
  rw [hI]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n q with h | h
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => χ.norm_le_one _).trans ?_
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast h.le
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      rw [Finset.sum_range_add]
      have := hper (1 + m)
      simp only [← add_assoc]
      rw [this, add_zero]
      exact ih m (by omega)

section General

variable {f : ℕ → ℂ} {C : ℝ}

noncomputable def summatory (f : ℕ → ℂ) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

/- English proof (translation)
The claim follows from `(measurable_from_top (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor`.
-/
theorem measurable_summatory (f : ℕ → ℂ) : Measurable (summatory f) :=
  (measurable_from_top (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

/- English proof (translation)
Simplify using `[summatory, Nat.floor_eq_zero.2 ht]`.
-/
theorem summatory_eq_zero {t : ℝ} (ht : t < 1) : summatory f t = 0 := by
  simp [summatory, Nat.floor_eq_zero.2 ht]

/- English proof (translation)
Rewrite using `[mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi (s := Set.Ici (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans_le (Set.mem_Ici.1 ht))), integral_Ici_eq_integral_Ioi]`. Use `setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_` and prove the remaining obligations. Simplify using `only [summatory, smul_eq_mul]`. Rewrite using `[mul_comm]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Introduce `t ht`. Rewrite using `[summatory_eq_zero (not_le.1 ht.2), smul_zero]`.
-/
theorem mellin_summatory (s : ℂ) :
    mellin (summatory f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ici (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans_le (Set.mem_Ici.1 ht))), integral_Ici_eq_integral_Ioi]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [summatory, smul_eq_mul]
    rw [mul_comm]
    congr 2
    ring
  · intro t ht
    rw [summatory_eq_zero (not_le.1 ht.2), smul_zero]

/- English proof (translation)
Establish `h : DifferentiableAt ℂ (mellin (summatory f)) (-s)`. Use `mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `LocallyIntegrable.locallyIntegrableOn ?_ _` and prove the remaining obligations. Use `(locallyIntegrable_const C).mono (measurable_summatory f).aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `Eventually.of_forall fun t => (hC _).trans (Real.le_norm_self C)`.

Use `IsBigO.of_bound C (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify `hC ⌊t⌋₊` using `[summatory]`. Simplify using `using hs`. Use `IsBigO.of_bound 0 ?_ filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht` and prove the remaining obligations. Simplify using `[summatory_eq_zero ht]`.

Simplify using the standard rewrite rules. Conclude with `h.comp s differentiableAt_id.neg`.
-/
theorem differentiableAt_mellin_summatory (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (summatory f) (-z)) s := by
  have h : DifferentiableAt ℂ (mellin (summatory f)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const C).mono (measurable_summatory f).aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => (hC _).trans (Real.le_norm_self C)
    · refine IsBigO.of_bound C (Eventually.of_forall fun t => ?_)
      simpa [summatory] using hC ⌊t⌋₊
    · simpa using hs
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
      simp [summatory_eq_zero ht]
    · simp
  exact h.comp s differentiableAt_id.neg

/- English proof (translation)
Rewrite using `[mellin_summatory]`. Establish `hlt : -(s.re + 1) < -1` using `by linarith`. Use `(norm_integral_le_of_norm_le (g := fun t : ℝ => C * t ^ (-(s.re + 1))) ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_).trans ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)` and prove the remaining obligations. Establish `ht0 : 0 < t` using `zero_lt_one.trans ht`.

Rewrite using `[norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]`. Simplify using `only [neg_re, add_re, one_re]`. Conclude with `mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg ht0.le _)`. Rewrite using `[integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]`. Use `le_of_eq ?_` and prove the remaining obligations.

Establish `: -(s.re + 1) + 1 = -s.re` using `by ring`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
theorem norm_mellin_summatory_le (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mellin (summatory f) (-s)‖ ≤ C / s.re := by
  rw [mellin_summatory]
  have hlt : -(s.re + 1) < -1 := by linarith
  refine (norm_integral_le_of_norm_le (g := fun t : ℝ => C * t ^ (-(s.re + 1)))
    ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg ht0.le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]
    refine le_of_eq ?_
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this]
    field_simp

end General

/- English proof (translation)
Establish `hC` using `norm_partialSum_le q χ hχ`. Establish `hU : IsOpen {z : ℂ | 0 < z.re}` using `isOpen_lt continuous_const continuous_re`. Establish `h1 : AnalyticOnNhd ℂ (LFunction χ) {z : ℂ | 0 < z.re}` using `(differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU`. Establish `h2 : AnalyticOnNhd ℂ (fun z => z * mellin (summatory fun n => χ (n : ZMod q)) (-z)) {z : ℂ | 0 < z.re}`. Use `DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU` and prove the remaining obligations.

Conclude with `(differentiableAt_id.mul (differentiableAt_mellin_summatory hC hz)).differentiableWithinAt`. Use `h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp) ?_ hs` and prove the remaining obligations. Establish `hV : IsOpen {z : ℂ | 1 < z.re}` using `isOpen_lt continuous_const continuous_re`. Use `filter_upwards [hV.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz`. Rewrite using `[LFunction_eq_LSeries χ hz, mellin_summatory]`.

Use `LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz) (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz) ?_` and prove the remaining obligations. Use `IsBigO.of_bound q (Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Simplify using `using hC n`.
-/
theorem LFunction_eq_mul_mellin (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * mellin (summatory fun n => χ (n : ZMod q)) (-s) := by
  have hC := norm_partialSum_le q χ hχ
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have h1 : AnalyticOnNhd ℂ (LFunction χ) {z : ℂ | 0 < z.re} :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have h2 : AnalyticOnNhd ℂ (fun z => z * mellin (summatory fun n => χ (n : ZMod q)) (-z))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_id.mul
      (differentiableAt_mellin_summatory hC hz)).differentiableWithinAt
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by simp) ?_ hs
  have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hV.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz
  rw [LFunction_eq_LSeries χ hz, mellin_summatory]
  refine LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz) ?_
  refine IsBigO.of_bound q (Eventually.of_forall fun n => ?_)
  simpa using hC n

/- English proof (translation)
Introduce `q _ χ hχ s hs`. Rewrite using `[LFunction_eq_mul_mellin q χ hχ hs, norm_mul]`. Use `(mul_le_mul_of_nonneg_left (norm_mellin_summatory_le (norm_partialSum_le q χ hχ) hs) (norm_nonneg s)).trans ?_` and prove the remaining obligations. Conclude with `le_of_eq (by ring)`.
-/
theorem norm_LFunction_le : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ s : ℂ, 0 < s.re → ‖LFunction χ s‖ ≤ q * ‖s‖ / s.re := by
  intro q _ χ hχ s hs
  rw [LFunction_eq_mul_mellin q χ hχ hs, norm_mul]
  refine (mul_le_mul_of_nonneg_left
    (norm_mellin_summatory_le (norm_partialSum_le q χ hχ) hs) (norm_nonneg s)).trans ?_
  exact le_of_eq (by ring)

end GlobalTheory.LGrowth
