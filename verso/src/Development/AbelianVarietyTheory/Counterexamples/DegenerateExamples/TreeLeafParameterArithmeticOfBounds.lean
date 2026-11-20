import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric

open Formalism.L2.Indef Formalism.L2.Indef.Tree NumberField

noncomputable section

namespace GlobalTheory.SizeLeafCheck

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def degenerate (O : FunData K Df) : FunData K Df :=
  { O with S0 := ∅, g1 := 0, g2 := 0, pd := 0, pd' := 0, dE := 0, Bw := 1 }

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[FunData.PPF, degenerate]`. Unfold `FunData.Sig0`. Conclude with `Finset.sum_empty`. Unfold `FunData.cS`.

Conclude with `Finset.sum_empty`.
-/
theorem degenerate_numbers (O : FunData K Df) (C b : ℝ) :
    (degenerate O).PPF C b = 0 ∧ (degenerate O).Sig0 C b = 0 ∧ (degenerate O).cS = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FunData.PPF, degenerate]
  · unfold FunData.Sig0; exact Finset.sum_empty
  · unfold FunData.cS; exact Finset.sum_empty

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `degenerate_numbers O C b`. Establish `hl : 0 ≤ Real.log b` using `Real.log_nonneg hb`. Use `⟨⟨fun q hq => absurd hq (Finset.notMem_empty q), by rw [h1, h2]; norm_num⟩, ?_, ?_⟩` and prove the remaining obligations. Unfold `LeafCS`. Rewrite using `[h3]`.

Check the signs of the components of the expression. Use `⟨le_refl _, ?_, ?_⟩` and prove the remaining obligations. Use `show (1 : ℝ) ≤ C * b`. Use the polynomial consequences of the given equalities and inequalities. Use `show Real.log 1 ≤ C * Real.log b`.

Rewrite using `[Real.log_one]`. Check the signs of the components of the expression.
-/
theorem degenerate_leaves (O : FunData K Df) (C b : ℝ) (hC : 1 ≤ C) (hb : 1 ≤ b) :
    PrimePowerModuliSumBound (degenerate O) C b ∧ LeafCS (degenerate O) b ∧ LeafWt (degenerate O) C b := by
  obtain ⟨h1, h2, h3⟩ := degenerate_numbers O C b
  have hl : 0 ≤ Real.log b := Real.log_nonneg hb
  refine ⟨⟨fun q hq => absurd hq (Finset.notMem_empty q), by rw [h1, h2]; norm_num⟩, ?_, ?_⟩
  · unfold LeafCS; rw [h3]; positivity
  · refine ⟨le_refl _, ?_, ?_⟩
    · show (1 : ℝ) ≤ C * b
      nlinarith
    · show Real.log 1 ≤ C * Real.log b
      rw [Real.log_one]; positivity

/- English proof (translation)
Introduce and unpack `⟨h, -⟩`. Conclude with `absurd h (by norm_num)`.
-/
theorem weight_free (O : FunData K Df) (C b : ℝ) : ¬ LeafWt { O with Bw := 0 } C b := by
  rintro ⟨h, -⟩
  exact absurd h (by norm_num)

/- English proof (translation)
Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (O.pol C b) hx`. Conclude with `⟨n, by unfold LeafPol; rw [Real.rpow_natCast]; exact hn.le⟩`.
-/
theorem exponent_free (O : FunData K Df) (C x b : ℝ) (hx : 1 < x) : ∃ CH : ℝ, LeafPol O C x CH b := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (O.pol C b) hx
  exact ⟨n, by unfold LeafPol; rw [Real.rpow_natCast]; exact hn.le⟩

/- English proof (translation)
Unfold `FunData.ga`. Use `max_le_max (max_le_max (Nat.ceil_mono ?_) le_rfl) le_rfl` and prove the remaining obligations. Establish `h1 : (0 : ℝ) ≤ (O.N : ℝ) ^ 3` using `by positivity`. Establish `h2 : (0 : ℝ) ≤ (O.nr : ℝ) ^ 7` using `by positivity`. Establish `h3 : (0 : ℝ) ≤ (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)` using `by positivity`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h h1, mul_le_mul_of_nonneg_right h h2, mul_le_mul_of_nonneg_right h h3]`.
-/
theorem ga_mono (O : FunData K Df) {C C' : ℝ} (h : C ≤ C') : O.ga C ≤ O.ga C' := by
  unfold FunData.ga
  refine max_le_max (max_le_max (Nat.ceil_mono ?_) le_rfl) le_rfl
  have h1 : (0 : ℝ) ≤ (O.N : ℝ) ^ 3 := by positivity
  have h2 : (0 : ℝ) ≤ (O.nr : ℝ) ^ 7 := by positivity
  have h3 : (0 : ℝ) ≤ (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h h1, mul_le_mul_of_nonneg_right h h2, mul_le_mul_of_nonneg_right h h3]

/- English proof (translation)
Establish `h2 : (0 : ℝ) ≤ C * (O.nr : ℝ) ^ 7` using `by positivity`. Establish `h3 : (0 : ℝ) ≤ C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)` using `by positivity`. Establish `h` using `Nat.le_ceil (C * (O.N : ℝ) ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ))`. Establish `h' : (⌈C * (O.N : ℝ) ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊ : ℝ) ≤ O.ga C`. Unfold `FunData.ga`.

Conclude with `le_trans (le_max_left _ _) (le_max_left _ _)` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_ga (O : FunData K Df) {C : ℝ} (hC : 0 ≤ C) : C * (O.N : ℝ) ^ 3 ≤ O.ga C := by
  have h2 : (0 : ℝ) ≤ C * (O.nr : ℝ) ^ 7 := by positivity
  have h3 : (0 : ℝ) ≤ C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ) := by positivity
  have h := Nat.le_ceil (C * (O.N : ℝ) ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ))
  have h' : (⌈C * (O.N : ℝ) ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊ : ℝ) ≤ O.ga C := by
    unfold FunData.ga
    exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)
  linarith

/- English proof (translation)
Establish `h` using `le_ga O hC`. Establish `h1 : (1 : ℝ) ≤ (O.N : ℝ) ^ 3` using `one_le_pow₀ (by exact_mod_cast hN)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ga_gt (O : FunData K Df) (hN : 1 ≤ O.N) (b C : ℝ) (hC : 0 ≤ C) (hb : b < C) : b < O.ga C := by
  have h := le_ga O hC
  have h1 : (1 : ℝ) ≤ (O.N : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hN)
  nlinarith

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨hm2n, hmkn, hm4fn, hfkn⟩` from `h1`. Establish `hm2 : (2 : ℝ) ≤ O.m` using `by exact_mod_cast hm2n`. Establish `hm4f : (O.m : ℝ) ^ 4 ≤ O.f` using `by exact_mod_cast hm4fn`. Establish `hfk : (O.f : ℝ) ≤ O.k` using `by exact_mod_cast hfkn`. Establish `hf16 : (16 : ℝ) ≤ O.f` using `by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm2 4]`.

Establish `hr : O.r = (O.k : ℝ) + O.m - 1` using `rfl`. Establish `hnr : (O.nr : ℝ) = O.r + 1` using `by unfold FunData.nr; push_cast; linarith`. Establish `hs : (O.s : ℝ) = O.r + 6` using `by unfold FunData.s; push_cast; linarith`. Establish `hr17 : 17 ≤ O.r` using `by linarith`. Establish `hmr : (O.m : ℝ) ≤ O.r` using `by linarith`.

Use `set r := O.r`. Use `set N : ℝ := (O.N : ℝ)`. Use `set m : ℝ := (O.m : ℝ)`. Establish `hnp : O.np ≤ 2 * m * r` using `by unfold FunData.np; nlinarith`. Establish `hnp1 : 1 ≤ O.np` using `by unfold FunData.np; nlinarith`.

Establish `hn4 : (r + 1) ^ 4 ≤ N`. Establish `: (r + 1) ^ 4 ≤ (2 * r) ^ 4` using `pow_le_pow_left₀ (by linarith) (by linarith) 4`. Use polynomial arithmetic with `[pow_nonneg (by linarith : 0 ≤ r) 4]`. Establish `hn1 : 1 ≤ r + 1` using `by linarith`. Establish `hn3 : (r + 1) ^ 3 ≤ N` using `(pow_le_pow_right₀ hn1 (by norm_num)).trans hn4`.

Establish `hnN : r + 1 ≤ N`. Use `(pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ 4)).trans hn4` as an intermediate fact. Simplify using `using this`. Establish `hN1 : 18 ≤ N` using `by linarith`. Establish `hN3 : N ≤ N ^ 3` using `le_self_pow₀ (by linarith) (by norm_num)`.

Establish `hN23 : 18 * N ^ 2 ≤ N ^ 3`. Use `mul_le_mul_of_nonneg_right hN1 (sq_nonneg N)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn7 : (r + 1) ^ 7 ≤ N ^ 3`. Establish `: (r + 1) ^ 7 = (r + 1) ^ 4 * (r + 1) ^ 3` using `by ring`.

Rewrite using `[this]`. Use `mul_le_mul hn4 hn3 (by positivity) (by linarith)` as an intermediate fact. Combine the linear relations using `[sq_nonneg N]`. Establish `hmN2 : m * N ^ 2 * 16 ≤ b`. Establish `: m * N ^ 2 * 16 ≤ m * N ^ 2 * O.f` using `mul_le_mul_of_nonneg_left hf16 (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN2b : 32 * N ^ 2 ≤ b`. Use `mul_le_mul_of_nonneg_right hm2 (sq_nonneg N)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb1 : 10000 ≤ b`.

Use `mul_le_mul hN1 hN1 (by norm_num) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set u := Real.sqrt b with hu`. Establish `hu2 : u * u = b` using `Real.mul_self_sqrt (by linarith)`. Establish `hu0 : 0 ≤ u` using `Real.sqrt_nonneg _`.

Establish `hu100 : 100 ≤ u` using `Real.le_sqrt_of_sq_le (by linarith)`. Establish `hNu : N ≤ u` using `Real.le_sqrt_of_sq_le (by linarith [sq_nonneg N])`. Establish `hsl : Real.sqrt (O.Lc : ℝ) ≤ u` using `Real.sqrt_le_sqrt h7`. Establish `hsm : Real.sqrt m ≤ r + 1` using `Real.sqrt_le_iff.mpr ⟨by linarith, le_trans (by linarith) (le_self_pow₀ hn1 two_ne_zero)⟩`. Establish `hP : 0 ≤ C * N ^ 3` using `by positivity`.

Establish `hP1 : N ^ 3 ≤ C * N ^ 3` using `le_mul_of_one_le_left (by positivity) hC`. Establish `hPu : 100 * (C * N ^ 3) ≤ C * N ^ 3 * u`. Use `mul_le_mul_of_nonneg_left hu100 hP` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hga : (O.ga C : ℝ) + 1 ≤ 2 * (C * N ^ 3 * u)`.

Establish `a1 : (⌈C * N ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊ : ℝ) + 1 ≤ 2 * (C * N ^ 3 * u)`. Use `Nat.ceil_lt_add_one (a := C * N ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)) (by positivity)` as an intermediate fact. Rewrite `this`, the goal using `[hnr]`. Establish `e1 : C * (r + 1) ^ 7 ≤ C * N ^ 3` using `mul_le_mul_of_nonneg_left hn7 (by linarith)`. Establish `e2 : C * (r + 1) ^ 3 * Real.sqrt (O.Lc : ℝ) ≤ C * N ^ 3 * u` using `mul_le_mul (mul_le_mul_of_nonneg_left (hn3.trans hN3) (by linarith)) hsl (Real.sqrt_nonneg _) hP`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `a2 : ((2 * O.N ^ 3 + 2 * O.s + 3 : ℕ) : ℝ) + 1 ≤ 2 * (C * N ^ 3 * u)` using `by push_cast; rw [hs]; linarith`. Establish `a3 : (⌈48 * (O.nr : ℝ) ^ 2 * Real.sqrt m⌉₊ : ℝ) + 1 ≤ 2 * (C * N ^ 3 * u)`. Use `Nat.ceil_lt_add_one (a := 48 * (O.nr : ℝ) ^ 2 * Real.sqrt m) (by positivity)` as an intermediate fact. Rewrite `this`, the goal using `[hnr]`.

Establish `e1 : 48 * (r + 1) ^ 2 * Real.sqrt m ≤ 48 * (r + 1) ^ 2 * (r + 1)` using `mul_le_mul_of_nonneg_left hsm (by positivity)`. Establish `e2 : 48 * (r + 1) ^ 2 * (r + 1) = 48 * (r + 1) ^ 3` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `FunData.ga`. Rewrite using `[Nat.cast_max, Nat.cast_max]`.

Break down `max_choice (max (⌈C * N ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊ : ℝ) ((2 * O.N ^ 3 + 2 * O.s + 3 : ℕ) : ℝ)) (⌈48 * (O.nr : ℝ) ^ 2 * Real.sqrt m⌉₊ : ℝ) with h | h` into its components or cases. Rewrite using `[h]`. Apply the tactic sequence `rcases max_choice (⌈C * N ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊ : ℝ) ((2 * O.N ^ 3 + 2 * O.s + 3 : ℕ) : ℝ) with h' | h' <;> rw [h'] <;> assumption`. Rewrite using `[h]`. Conclude with `a3`.

Establish `hnpb : O.np ≤ b`. Establish `: 2 * m * r ≤ 2 * m * N` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `: 2 * m * N ≤ m * N ^ 2 * 16`. Use `mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ 16 * N by linarith) (mul_nonneg (by linarith : (0:ℝ) ≤ m) (by linarith : (0:ℝ) ≤ N))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hRp : O.Rp C ≤ C * m * N ^ 3 * b`. Unfold `FunData.Rp`. Establish `e1 : (m + 1) * ((O.ga C : ℝ) + 1) ≤ (2 * m) * (2 * (C * N ^ 3 * u))` using `mul_le_mul (by linarith) hga (by positivity) (by linarith)`. Establish `hQ : 0 ≤ m * (C * N ^ 3) * u` using `by positivity`.

Establish `e2 : 100 * (m * (C * N ^ 3) * u) ≤ C * m * N ^ 3 * b`. Establish `t1` using `mul_le_mul_of_nonneg_left hu100 hQ`. Establish `t2 : m * (C * N ^ 3) * u * u = C * m * N ^ 3 * b`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e3 : 4 * b ≤ C * m * N ^ 3 * b`. Establish `t1 : 4 ≤ C * m * N ^ 3`. Use `mul_le_mul hm2 (show (2 : ℝ) ≤ C * N ^ 3 by linarith) (by norm_num) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_le_mul_of_nonneg_right t1 (by linarith)`.

Establish `h7' : (O.Lc : ℝ) ≤ b` using `h7`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hb, hN, hnp, hRp, ?_⟩` and prove the remaining obligations. Establish `hRp0 : 0 < O.Rp C`. Unfold `FunData.Rp`.

Establish `: (0 : ℝ) ≤ (m + 1) * ((O.ga C : ℝ) + 1) + O.Lc` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4 : C * m * N ^ 3 * b ≤ C * u ^ 5`. Establish `: m * N ^ 3 ≤ b * u`. Establish `: m * N ^ 3 = (m * N ^ 2) * N` using `by ring`.

Rewrite using `[this]`. Conclude with `mul_le_mul (by linarith [mul_nonneg (by linarith : (0:ℝ) ≤ m) (sq_nonneg N)]) hNu (by linarith) (by linarith)`. Establish `h5 : u ^ 5 = b * u * b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h5, mul_assoc C, mul_assoc C]`.

Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (by linarith)) (by linarith)`. Establish `e5 : O.np * O.Rp C ≤ (2 * C) * u ^ 7`. Use `mul_le_mul hnpb (hRp.trans e4) hRp0.le (by linarith)` as an intermediate fact. Establish `h7 : b * (C * u ^ 5) = C * u ^ 7`. Combine the equalities or inequalities in the displayed calculation.

Establish `: 0 ≤ C * u ^ 7` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e6` using `Real.log_le_log (by positivity) e5`. Rewrite `e6` using `[Real.log_mul (x := 2 * C) (by positivity) (by positivity), Real.log_pow, hu, Real.log_sqrt (by linarith)]`. Move the coercions through the operations in `at e6`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tree_leaf_parameter_arithmetic_of_bounds (O : FunData K Df) (C b : ℝ) (hC : 1 ≤ C) (h1 : leafHypothesesConst O) (h7 : LatticeConstantBound O b)
    (hb : (O.m : ℝ) * O.f * (O.N : ℝ) ^ 2 ≤ b) (hN : 80 * O.r ^ 4 ≤ O.N)
    (hL : 2 * Real.log (2 * C) ≤ Real.log b) : DegreeAndSizeBounds O C b := by
  obtain ⟨hm2n, hmkn, hm4fn, hfkn⟩ := h1
  have hm2 : (2 : ℝ) ≤ O.m := by exact_mod_cast hm2n
  have hm4f : (O.m : ℝ) ^ 4 ≤ O.f := by exact_mod_cast hm4fn
  have hfk : (O.f : ℝ) ≤ O.k := by exact_mod_cast hfkn
  have hf16 : (16 : ℝ) ≤ O.f := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm2 4]
  have hr : O.r = (O.k : ℝ) + O.m - 1 := rfl
  have hnr : (O.nr : ℝ) = O.r + 1 := by unfold FunData.nr; push_cast; linarith
  have hs : (O.s : ℝ) = O.r + 6 := by unfold FunData.s; push_cast; linarith
  have hr17 : 17 ≤ O.r := by linarith
  have hmr : (O.m : ℝ) ≤ O.r := by linarith
  set r := O.r
  set N : ℝ := (O.N : ℝ)
  set m : ℝ := (O.m : ℝ)
  have hnp : O.np ≤ 2 * m * r := by unfold FunData.np; nlinarith
  have hnp1 : 1 ≤ O.np := by unfold FunData.np; nlinarith
  have hn4 : (r + 1) ^ 4 ≤ N := by
    have : (r + 1) ^ 4 ≤ (2 * r) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    nlinarith [pow_nonneg (by linarith : 0 ≤ r) 4]
  have hn1 : 1 ≤ r + 1 := by linarith
  have hn3 : (r + 1) ^ 3 ≤ N := (pow_le_pow_right₀ hn1 (by norm_num)).trans hn4
  have hnN : r + 1 ≤ N := by
    have := (pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ 4)).trans hn4
    simpa using this
  have hN1 : 18 ≤ N := by linarith
  have hN3 : N ≤ N ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hN23 : 18 * N ^ 2 ≤ N ^ 3 := by
    have := mul_le_mul_of_nonneg_right hN1 (sq_nonneg N)
    linarith
  have hn7 : (r + 1) ^ 7 ≤ N ^ 3 := by
    have : (r + 1) ^ 7 = (r + 1) ^ 4 * (r + 1) ^ 3 := by ring
    rw [this]
    have := mul_le_mul hn4 hn3 (by positivity) (by linarith)
    linarith [sq_nonneg N]
  have hmN2 : m * N ^ 2 * 16 ≤ b := by
    have : m * N ^ 2 * 16 ≤ m * N ^ 2 * O.f := mul_le_mul_of_nonneg_left hf16 (by positivity)
    linarith
  have hN2b : 32 * N ^ 2 ≤ b := by
    have := mul_le_mul_of_nonneg_right hm2 (sq_nonneg N)
    linarith
  have hb1 : 10000 ≤ b := by
    have := mul_le_mul hN1 hN1 (by norm_num) (by linarith)
    linarith
  set u := Real.sqrt b with hu
  have hu2 : u * u = b := Real.mul_self_sqrt (by linarith)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu100 : 100 ≤ u := Real.le_sqrt_of_sq_le (by linarith)
  have hNu : N ≤ u := Real.le_sqrt_of_sq_le (by linarith [sq_nonneg N])
  have hsl : Real.sqrt (O.Lc : ℝ) ≤ u := Real.sqrt_le_sqrt h7
  have hsm : Real.sqrt m ≤ r + 1 := Real.sqrt_le_iff.mpr ⟨by linarith,
    le_trans (by linarith) (le_self_pow₀ hn1 two_ne_zero)⟩
  have hP : 0 ≤ C * N ^ 3 := by positivity
  have hP1 : N ^ 3 ≤ C * N ^ 3 := le_mul_of_one_le_left (by positivity) hC
  have hPu : 100 * (C * N ^ 3) ≤ C * N ^ 3 * u := by
    have := mul_le_mul_of_nonneg_left hu100 hP
    linarith
  have hga : (O.ga C : ℝ) + 1 ≤ 2 * (C * N ^ 3 * u) := by
    have a1 : (⌈C * N ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊ : ℝ) + 1 ≤
        2 * (C * N ^ 3 * u) := by
      have := Nat.ceil_lt_add_one (a := C * N ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ))
        (by positivity)
      rw [hnr] at this ⊢
      have e1 : C * (r + 1) ^ 7 ≤ C * N ^ 3 := mul_le_mul_of_nonneg_left hn7 (by linarith)
      have e2 : C * (r + 1) ^ 3 * Real.sqrt (O.Lc : ℝ) ≤ C * N ^ 3 * u :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hn3.trans hN3) (by linarith)) hsl (Real.sqrt_nonneg _) hP
      linarith
    have a2 : ((2 * O.N ^ 3 + 2 * O.s + 3 : ℕ) : ℝ) + 1 ≤ 2 * (C * N ^ 3 * u) := by
      push_cast; rw [hs]; linarith
    have a3 : (⌈48 * (O.nr : ℝ) ^ 2 * Real.sqrt m⌉₊ : ℝ) + 1 ≤ 2 * (C * N ^ 3 * u) := by
      have := Nat.ceil_lt_add_one (a := 48 * (O.nr : ℝ) ^ 2 * Real.sqrt m) (by positivity)
      rw [hnr] at this ⊢
      have e1 : 48 * (r + 1) ^ 2 * Real.sqrt m ≤ 48 * (r + 1) ^ 2 * (r + 1) :=
        mul_le_mul_of_nonneg_left hsm (by positivity)
      have e2 : 48 * (r + 1) ^ 2 * (r + 1) = 48 * (r + 1) ^ 3 := by ring
      linarith
    unfold FunData.ga
    rw [Nat.cast_max, Nat.cast_max]
    rcases max_choice (max (⌈C * N ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊ : ℝ)
      ((2 * O.N ^ 3 + 2 * O.s + 3 : ℕ) : ℝ)) (⌈48 * (O.nr : ℝ) ^ 2 * Real.sqrt m⌉₊ : ℝ) with h | h
    · rw [h]
      rcases max_choice (⌈C * N ^ 3 + C * (O.nr : ℝ) ^ 7 + C * (O.nr : ℝ) ^ 3 * Real.sqrt (O.Lc : ℝ)⌉₊ : ℝ)
        ((2 * O.N ^ 3 + 2 * O.s + 3 : ℕ) : ℝ) with h' | h' <;> rw [h'] <;> assumption
    · rw [h]; exact a3
  have hnpb : O.np ≤ b := by
    have : 2 * m * r ≤ 2 * m * N := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have : 2 * m * N ≤ m * N ^ 2 * 16 := by
      have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ 16 * N by linarith)
        (mul_nonneg (by linarith : (0:ℝ) ≤ m) (by linarith : (0:ℝ) ≤ N))
      linarith
    linarith
  have hRp : O.Rp C ≤ C * m * N ^ 3 * b := by
    unfold FunData.Rp
    have e1 : (m + 1) * ((O.ga C : ℝ) + 1) ≤ (2 * m) * (2 * (C * N ^ 3 * u)) :=
      mul_le_mul (by linarith) hga (by positivity) (by linarith)
    have hQ : 0 ≤ m * (C * N ^ 3) * u := by positivity
    have e2 : 100 * (m * (C * N ^ 3) * u) ≤ C * m * N ^ 3 * b := by
      have t1 := mul_le_mul_of_nonneg_left hu100 hQ
      have t2 : m * (C * N ^ 3) * u * u = C * m * N ^ 3 * b := by
        calc _ = C * m * N ^ 3 * (u * u) := by ring
          _ = _ := by rw [hu2]
      linarith
    have e3 : 4 * b ≤ C * m * N ^ 3 * b := by
      have t1 : 4 ≤ C * m * N ^ 3 := by
        have := mul_le_mul hm2 (show (2 : ℝ) ≤ C * N ^ 3 by linarith) (by norm_num) (by linarith)
        linarith
      exact mul_le_mul_of_nonneg_right t1 (by linarith)
    have h7' : (O.Lc : ℝ) ≤ b := h7
    linarith
  refine ⟨hb, hN, hnp, hRp, ?_⟩
  have hRp0 : 0 < O.Rp C := by
    unfold FunData.Rp
    have : (0 : ℝ) ≤ (m + 1) * ((O.ga C : ℝ) + 1) + O.Lc := by positivity
    linarith
  have e4 : C * m * N ^ 3 * b ≤ C * u ^ 5 := by
    have : m * N ^ 3 ≤ b * u := by
      have : m * N ^ 3 = (m * N ^ 2) * N := by ring
      rw [this]
      exact mul_le_mul (by linarith [mul_nonneg (by linarith : (0:ℝ) ≤ m) (sq_nonneg N)]) hNu (by linarith) (by linarith)
    have h5 : u ^ 5 = b * u * b := by
      calc _ = (u * u) * u * (u * u) := by ring
        _ = _ := by rw [hu2]
    rw [h5, mul_assoc C, mul_assoc C]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (by linarith)) (by linarith)
  have e5 : O.np * O.Rp C ≤ (2 * C) * u ^ 7 := by
    have := mul_le_mul hnpb (hRp.trans e4) hRp0.le (by linarith)
    have h7 : b * (C * u ^ 5) = C * u ^ 7 := by
      calc _ = (u * u) * (C * u ^ 5) := by rw [hu2]
        _ = _ := by ring
    have : 0 ≤ C * u ^ 7 := by positivity
    linarith
  have e6 := Real.log_le_log (by positivity) e5
  rw [Real.log_mul (x := 2 * C) (by positivity) (by positivity), Real.log_pow, hu, Real.log_sqrt (by linarith)] at e6
  push_cast at e6
  linarith

/- English proof (translation)
Establish `hf' : (1 : ℝ) ≤ O.f` using `by exact_mod_cast hf`. Establish `hfL : Real.log b ≤ O.f * Real.log b` using `by nlinarith`. Establish `hfL' : (O.f : ℝ) ≤ O.f * Real.log b` using `by nlinarith`. Establish `hlq : 0 < Real.log (O.qq O.sv0)` using `Real.log_pos (by exact_mod_cast (hq _ h0).one_lt)`. Establish `hP0 : 0 ≤ O.PPF C b` using `by nlinarith`.

Use `⟨⟨hq, ?_⟩, ?_⟩` and prove the remaining obligations. Unfold `FunData.Sig0`. Rewrite using `[← Finset.add_sum_erase _ _ h0]`. Establish `e1 : ∑ q ∈ O.S0.erase O.sv0, (O.ee C b q : ℝ) * Real.log (O.qq q) = 2 * ∑ q ∈ O.S0.erase O.sv0, Real.log (O.qq q)`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun q hq' => ?_` and prove the remaining obligations. Simplify using `[FunData.ee, Finset.ne_of_mem_erase hq']`. Establish `e2 : (O.ee C b O.sv0 : ℝ) * Real.log (O.qq O.sv0) ≤ O.PPF C b + Real.log (O.qq O.sv0)`. Establish `h` using `Nat.floor_le (div_nonneg hP0 hlq.le)`. Rewrite `h` using `[le_div_iff₀ hlq]`.

Simplify using `only [FunData.ee, if_true]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e1]`. Use the polynomial consequences of the given equalities and inequalities.

Unfold `LeafCS FunData.cS`. Rewrite using `[← Finset.add_sum_erase _ _ h0]`. Establish `e1 : ∑ q ∈ O.S0.erase O.sv0, (O.cc q : ℝ) * Real.log (O.qq q) ≤ 2 * ∑ q ∈ O.S0.erase O.sv0, Real.log (O.qq q)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun q hq' => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)` and prove the remaining obligations.

Conclude with `hc q (Finset.mem_of_mem_erase hq')` after adjusting the coercions. Establish `e2 : (O.cc O.sv0 : ℝ) * Real.log (O.qq O.sv0) ≤ 1 * Real.log (O.qq O.sv0)` using `mul_le_mul_of_nonneg_right (by exact_mod_cast hc0) hlq.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem leaf_bounds_of_log_sizes (O : FunData K Df) [DecidableEq O.Sq] (C b : ℝ) (hL : 1 ≤ Real.log b) (hf : 1 ≤ O.f)
    (h0 : O.sv0 ∈ O.S0) (hq : ∀ q ∈ O.S0, IsPrimePow (O.qq q)) (hq0 : Real.log (O.qq O.sv0) ≤ Real.log b)
    (hS : ∑ q ∈ O.S0.erase O.sv0, Real.log (O.qq q) ≤ O.f * (20 * Real.log b + 2))
    (hc : ∀ q ∈ O.S0, O.cc q ≤ 2) (hc0 : O.cc O.sv0 ≤ 1) (hP : 45 * O.f * Real.log b ≤ O.PPF C b) :
    PrimePowerModuliSumBound O C b ∧ LeafCS O b := by
  have hf' : (1 : ℝ) ≤ O.f := by exact_mod_cast hf
  have hfL : Real.log b ≤ O.f * Real.log b := by nlinarith
  have hfL' : (O.f : ℝ) ≤ O.f * Real.log b := by nlinarith
  have hlq : 0 < Real.log (O.qq O.sv0) := Real.log_pos (by exact_mod_cast (hq _ h0).one_lt)
  have hP0 : 0 ≤ O.PPF C b := by nlinarith
  refine ⟨⟨hq, ?_⟩, ?_⟩
  · unfold FunData.Sig0
    rw [← Finset.add_sum_erase _ _ h0]
    have e1 : ∑ q ∈ O.S0.erase O.sv0, (O.ee C b q : ℝ) * Real.log (O.qq q) =
        2 * ∑ q ∈ O.S0.erase O.sv0, Real.log (O.qq q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq' => ?_
      simp [FunData.ee, Finset.ne_of_mem_erase hq']
    have e2 : (O.ee C b O.sv0 : ℝ) * Real.log (O.qq O.sv0) ≤ O.PPF C b + Real.log (O.qq O.sv0) := by
      have h := Nat.floor_le (div_nonneg hP0 hlq.le)
      rw [le_div_iff₀ hlq] at h
      simp only [FunData.ee, if_true]
      push_cast
      linarith
    rw [e1]; nlinarith
  · unfold LeafCS FunData.cS
    rw [← Finset.add_sum_erase _ _ h0]
    have e1 : ∑ q ∈ O.S0.erase O.sv0, (O.cc q : ℝ) * Real.log (O.qq q) ≤
        2 * ∑ q ∈ O.S0.erase O.sv0, Real.log (O.qq q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq' => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
      exact_mod_cast hc q (Finset.mem_of_mem_erase hq')
    have e2 : (O.cc O.sv0 : ℝ) * Real.log (O.qq O.sv0) ≤ 1 * Real.log (O.qq O.sv0) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc0) hlq.le
    nlinarith

end GlobalTheory.SizeLeafCheck
