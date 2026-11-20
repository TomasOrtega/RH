import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory
namespace LLeft

noncomputable def diffPow : ℕ → ℂ → ℝ → ℂ
  | 0, s, x => (x : ℂ) ^ (-s)
  | k + 1, s, x => diffPow k s x - diffPow k s (x + 1)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `x hx`. Distinguish the cases in `hs : s = 0`. Substitute `hs` using the available equality.

Establish `: diffPow 0 0 = fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `y`. Simplify using `[diffPow]`. Rewrite using `[this]`. Simplify using `using hasDerivAt_const x (1 : ℂ)`.

Establish `h` using `hasDerivAt_ofReal_cpow_const hx.ne' (r := -s) (neg_ne_zero.mpr hs)`. Establish `e : -s - 1 = -(s + 1)` using `by ring`. Rewrite `h` using `[e]`. Conclude with `h`. Consider the case `succ k ih`.

Introduce `x hx`. Establish `h1` using `ih x hx`. Establish `h2` using `(ih (x + 1) (by linarith)).comp_add_const x 1`. Establish `h3` using `h1.sub h2`. Establish `e : -s * diffPow (k + 1) (s + 1) x = -s * diffPow k (s + 1) x - -s * diffPow k (s + 1) (x + 1)`.

Simplify using `only [diffPow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h3`.
-/
theorem hasDerivAt_diffPow (k : ℕ) (s : ℂ) : ∀ x : ℝ, 0 < x →
    HasDerivAt (diffPow k s) (-s * diffPow k (s + 1) x) x := by
  induction k with
  | zero =>
    intro x hx
    by_cases hs : s = 0
    · subst hs
      have : diffPow 0 0 = fun _ => (1 : ℂ) := by
        funext y; simp [diffPow]
      rw [this]
      simpa using hasDerivAt_const x (1 : ℂ)
    · have h := hasDerivAt_ofReal_cpow_const hx.ne' (r := -s) (neg_ne_zero.mpr hs)
      have e : -s - 1 = -(s + 1) := by ring
      rw [e] at h
      exact h
  | succ k ih =>
    intro x hx
    have h1 := ih x hx
    have h2 := (ih (x + 1) (by linarith)).comp_add_const x 1
    have h3 := h1.sub h2
    have e : -s * diffPow (k + 1) (s + 1) x
        = -s * diffPow k (s + 1) x - -s * diffPow k (s + 1) (x + 1) := by
      simp only [diffPow]; ring
    rw [e]
    exact h3

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `s x hx _`. Simplify using `[diffPow, Complex.norm_cpow_eq_rpow_re_of_pos hx]`. Consider the case `succ k ih`.

Introduce `s x hx hs`. Establish `hs' : 0 ≤ (s + 1).re + k`. Simplify using `only [add_re, one_re]`. Move the coercions through the operations in `at hs`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `key` using `norm_image_sub_le_of_norm_deriv_le_segment' (f := diffPow k s) (f' := fun y => -s * diffPow k (s + 1) y) (a := x) (b := x + 1) (C := (‖s‖ + (k + 1 : ℕ)) ^ (k + 1) * x ^ (-(s.re + (k + 1 : ℕ)))) (fun y hy => (hasDerivAt_diffPow k s y (hx.trans_le hy.1)).hasDerivWithinAt) (by`. Introduce `y hy`. Establish `hy0 : 0 < y` using `hx.trans_le hy.1`. Establish `h1` using `ih (s + 1) y hy0 hs'`. Establish `h2 : y ^ (-((s + 1).re + k)) ≤ x ^ (-((s + 1).re + k))` using `Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith)`.

Establish `h3 : ‖s + 1‖ + k ≤ ‖s‖ + (k + 1 : ℕ)`. Use `norm_add_le s 1` as an intermediate fact. Use `push_cast`. Simplify using `only [norm_one] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4 : ‖s‖ ≤ ‖s‖ + (k + 1 : ℕ)` using `le_add_of_nonneg_right (by positivity)`. Establish `e : -(s.re + (k + 1 : ℕ)) = -((s + 1).re + k)`. Simplify using `only [add_re, one_re]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[norm_mul, norm_neg, e, pow_succ', mul_assoc]`. Use `mul_le_mul h4 (h1.trans ?_) (norm_nonneg _) (by positivity)` and prove the remaining obligations. Use the proof step `gcongr)`. Use the proof step `(x + 1) ⟨by linarith, le_rfl⟩`. Simplify using `only [diffPow]`.

Rewrite using `[norm_sub_rev]`. Simplify using `using key`.
-/
theorem norm_diffPow_le (k : ℕ) : ∀ (s : ℂ) (x : ℝ), 0 < x → 0 ≤ s.re + k →
    ‖diffPow k s x‖ ≤ (‖s‖ + k) ^ k * x ^ (-(s.re + k)) := by
  induction k with
  | zero =>
    intro s x hx _
    simp [diffPow, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  | succ k ih =>
    intro s x hx hs
    have hs' : 0 ≤ (s + 1).re + k := by
      simp only [add_re, one_re]; push_cast at hs; linarith
    have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := diffPow k s)
      (f' := fun y => -s * diffPow k (s + 1) y) (a := x) (b := x + 1)
      (C := (‖s‖ + (k + 1 : ℕ)) ^ (k + 1) * x ^ (-(s.re + (k + 1 : ℕ))))
      (fun y hy => (hasDerivAt_diffPow k s y (hx.trans_le hy.1)).hasDerivWithinAt)
      (by
        intro y hy
        have hy0 : 0 < y := hx.trans_le hy.1
        have h1 := ih (s + 1) y hy0 hs'
        have h2 : y ^ (-((s + 1).re + k)) ≤ x ^ (-((s + 1).re + k)) :=
          Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith)
        have h3 : ‖s + 1‖ + k ≤ ‖s‖ + (k + 1 : ℕ) := by
          have := norm_add_le s 1
          push_cast; simp only [norm_one] at this; linarith
        have h4 : ‖s‖ ≤ ‖s‖ + (k + 1 : ℕ) := le_add_of_nonneg_right (by positivity)
        have e : -(s.re + (k + 1 : ℕ)) = -((s + 1).re + k) := by
          simp only [add_re, one_re]; push_cast; ring
        rw [norm_mul, norm_neg, e, pow_succ', mul_assoc]
        refine mul_le_mul h4 (h1.trans ?_) (norm_nonneg _) (by positivity)
        gcongr)
      (x + 1) ⟨by linarith, le_rfl⟩
    simp only [diffPow]
    rw [norm_sub_rev]
    simpa using key

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `x hx`. Simplify using `only [diffPow]`. Conclude with `differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast hx.ne'))`.

Consider the case `succ k ih`. Introduce `x hx`. Simplify using `only [diffPow]`. Conclude with `(ih x hx).sub (ih (x + 1) (by linarith))`.
-/
theorem differentiable_diffPow (k : ℕ) : ∀ x : ℝ, 0 < x →
    Differentiable ℂ (fun s => diffPow k s x) := by
  induction k with
  | zero =>
    intro x hx
    simp only [diffPow]
    exact differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  | succ k ih =>
    intro x hx
    simp only [diffPow]
    exact (ih x hx).sub (ih (x + 1) (by linarith))

/- English proof (translation)
Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM 0)`. Use `set T : ℕ → ℂ := fun n => ∑ k ∈ Finset.range n, a k with hT`. Establish `hTp : Function.Periodic T q`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp [hT, h0]`. Consider the case `succ n ih`. Establish `e : n + 1 + q = (n + q) + 1` using `by ring`. Simplify using `only [hT] at ih ⊢`. Rewrite using `[e, Finset.sum_range_succ, Finset.sum_range_succ, ih, hp n]`.

Establish `hTb : ∀ n, ‖T n‖ ≤ q * M`. Introduce `n`. Rewrite using `[← hTp.map_mod_nat n]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(Nat.mod_lt n hq).le`.

Establish `hq' : (0 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hqc : (q : ℂ) ≠ 0` using `by exact_mod_cast hq.ne'`. Use `set μ : ℂ := (∑ n ∈ Finset.range q, T (n + 1)) / q with hμ`. Establish `hμb : ‖μ‖ ≤ q * M`. Rewrite using `[hμ, norm_div, Complex.norm_natCast, div_le_iff₀ hq']`.

Combine the equalities or inequalities in the displayed calculation. Establish `hbb : ∀ n, ‖T (n + 1) - μ‖ ≤ 2 * q * M` using `fun n => (norm_sub_le _ _).trans (by linarith [hTb (n + 1)])`. Use `⟨fun n => T (n + 1) - μ, μ, ?_, ?_, hbb, hμb, ?_⟩` and prove the remaining obligations. Introduce `n`. Establish `e : n + q + 1 = (n + 1) + q` using `by ring`.

Simplify using `only [e, hTp (n + 1)]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hμ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `f hf`.

Establish `hf1 : Summable (fun n => ‖f (n + 1)‖)` using `(summable_nat_add_iff 1).mpr hf`. Establish `sm : ∀ (c g : ℕ → ℂ) (K : ℝ), (∀ n, ‖c n‖ ≤ K) → Summable (fun n => ‖g n‖) → Summable (fun n => c n * g n)`. Introduce `c g K hc hg`. Use `Summable.of_norm_bounded (hg.mul_left K) fun n => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)`. Establish `s1` using `sm a f M hM hf`. Establish `s2` using `sm _ f _ hbb hf`. Establish `s3` using `sm _ _ _ hbb hf1`. Establish `s4` using `sm (fun n => T (n + 1 + 1) - μ) _ _ (fun n => hbb (n + 1)) hf1`.

Establish `e1 : ∀ n, a (n + 1) * f (n + 1) = (T (n + 1 + 1) - μ) * f (n + 1) - (T (n + 1) - μ) * f (n + 1)`. Introduce `n`. Simplify using `only [hT, Finset.sum_range_succ _ (n + 1)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mul_sub _ (f _)]`.

Rewrite using `[s1.tsum_eq_zero_add, s2.tsum_sub s3, s2.tsum_eq_zero_add]`. Simplify using `only [e1]`. Rewrite using `[s4.tsum_sub s3]`. Simplify using `only [hT, zero_add, Finset.sum_range_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abel_step (q : ℕ) (hq : 0 < q) (a : ℕ → ℂ) (M : ℝ) (hp : Function.Periodic a q)
    (h0 : ∑ n ∈ Finset.range q, a n = 0) (hM : ∀ n, ‖a n‖ ≤ M) :
    ∃ (b : ℕ → ℂ) (μ : ℂ), Function.Periodic b q ∧ ∑ n ∈ Finset.range q, b n = 0 ∧
      (∀ n, ‖b n‖ ≤ 2 * q * M) ∧ ‖μ‖ ≤ q * M ∧
      ∀ f : ℕ → ℂ, Summable (fun n => ‖f n‖) →
        ∑' n, a n * f n = μ * f 0 + ∑' n, b n * (f n - f (n + 1)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set T : ℕ → ℂ := fun n => ∑ k ∈ Finset.range n, a k with hT
  have hTp : Function.Periodic T q := by
    intro n
    induction n with
    | zero => simp [hT, h0]
    | succ n ih =>
      have e : n + 1 + q = (n + q) + 1 := by ring
      simp only [hT] at ih ⊢
      rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, hp n]
  have hTb : ∀ n, ‖T n‖ ≤ q * M := by
    intro n
    rw [← hTp.map_mod_nat n]
    calc ‖T (n % q)‖ ≤ ∑ k ∈ Finset.range (n % q), ‖a k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n % q), M := Finset.sum_le_sum fun k _ => hM k
      _ = (n % q : ℕ) * M := by simp
      _ ≤ q * M := by
        gcongr
        exact (Nat.mod_lt n hq).le
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  set μ : ℂ := (∑ n ∈ Finset.range q, T (n + 1)) / q with hμ
  have hμb : ‖μ‖ ≤ q * M := by
    rw [hμ, norm_div, Complex.norm_natCast, div_le_iff₀ hq']
    calc _ ≤ ∑ n ∈ Finset.range q, ‖T (n + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range q, q * M := Finset.sum_le_sum fun k _ => hTb _
      _ = _ := by simp; ring
  have hbb : ∀ n, ‖T (n + 1) - μ‖ ≤ 2 * q * M := fun n =>
    (norm_sub_le _ _).trans (by linarith [hTb (n + 1)])
  refine ⟨fun n => T (n + 1) - μ, μ, ?_, ?_, hbb, hμb, ?_⟩
  · intro n
    have e : n + q + 1 = (n + 1) + q := by ring
    simp only [e, hTp (n + 1)]
  · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hμ]
    field_simp
    ring
  · intro f hf
    have hf1 : Summable (fun n => ‖f (n + 1)‖) := (summable_nat_add_iff 1).mpr hf
    have sm : ∀ (c g : ℕ → ℂ) (K : ℝ), (∀ n, ‖c n‖ ≤ K) → Summable (fun n => ‖g n‖) →
        Summable (fun n => c n * g n) := by
      intro c g K hc hg
      refine Summable.of_norm_bounded (hg.mul_left K) fun n => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)
    have s1 := sm a f M hM hf
    have s2 := sm _ f _ hbb hf
    have s3 := sm _ _ _ hbb hf1
    have s4 := sm (fun n => T (n + 1 + 1) - μ) _ _ (fun n => hbb (n + 1)) hf1
    have e1 : ∀ n, a (n + 1) * f (n + 1)
        = (T (n + 1 + 1) - μ) * f (n + 1) - (T (n + 1) - μ) * f (n + 1) := by
      intro n
      simp only [hT, Finset.sum_range_succ _ (n + 1)]
      ring
    simp only [mul_sub _ (f _)]
    rw [s1.tsum_eq_zero_add, s2.tsum_sub s3, s2.tsum_eq_zero_add]
    simp only [e1]
    rw [s4.tsum_sub s3]
    simp only [hT, zero_add, Finset.sum_range_one]
    ring

/- English proof (translation)
Establish `h : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re + k)))`. Use `(summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -(s.re + k) < -1 by linarith))` as an intermediate fact. Simplify using `using this`. Conclude with `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_diffPow_le k s _ (by positivity) (by linarith)) (h.mul_left _)`.
-/
theorem summable_diffPow (k : ℕ) (s : ℂ) (hs : 1 < s.re + k) :
    Summable (fun n : ℕ => ‖diffPow k s ((n : ℝ) + 1)‖) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re + k))) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
      (show -(s.re + k) < -1 by linarith))
    simpa using this
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_diffPow_le k s _ (by positivity) (by linarith)) (h.mul_left _)

/- English proof (translation)
Take `⟨b₁, μ₁, p₁, z₁, n₁, m₁, e₁⟩` from `abel_step q hq a 1 hp h0 hM`. Take `⟨b₂, μ₂, p₂, z₂, n₂, m₂, e₂⟩` from `abel_step q hq b₁ _ p₁ z₁ n₁`. Take `⟨b₃, μ₃, -, -, n₃, m₃, e₃⟩` from `abel_step q hq b₂ _ p₂ z₂ n₂`. Use `⟨b₃, μ₁, μ₂, μ₃, fun n => (n₃ n).trans_eq (by ring), m₁.trans_eq (by ring), m₂.trans_eq (by ring), m₃.trans_eq (by ring), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hd : ∀ (k n : ℕ), diffPow k s ((n : ℝ) + 1) - diffPow k s (((n + 1 : ℕ) : ℝ) + 1) = diffPow (k + 1) s ((n : ℝ) + 1)`.

Introduce `k n`. Simplify using `only [diffPow]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hsum : ∀ k : ℕ, Summable (fun n : ℕ => ‖diffPow k s ((n : ℝ) + 1)‖)` using `fun k => summable_diffPow k s (by have : (0 : ℝ) ≤ k := by positivity linarith)`.

Establish `f₁` using `e₁ _ (hsum 0)`. Establish `f₂` using `e₂ _ (hsum 1)`. Establish `f₃` using `e₃ _ (hsum 2)`. Simplify using `only [hd] at f₁ f₂ f₃`. Simplify using `only [Nat.cast_zero, zero_add] at f₁ f₂ f₃`.

Rewrite using `[f₁, f₂, f₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abel_three (q : ℕ) (hq : 0 < q) (a : ℕ → ℂ) (hp : Function.Periodic a q)
    (h0 : ∑ n ∈ Finset.range q, a n = 0) (hM : ∀ n, ‖a n‖ ≤ 1) :
    ∃ (b : ℕ → ℂ) (μ₁ μ₂ μ₃ : ℂ), (∀ n, ‖b n‖ ≤ 8 * (q : ℝ) ^ 3) ∧ ‖μ₁‖ ≤ q ∧
      ‖μ₂‖ ≤ 2 * (q : ℝ) ^ 2 ∧ ‖μ₃‖ ≤ 4 * (q : ℝ) ^ 3 ∧
      ∀ s : ℂ, 1 < s.re → ∑' n : ℕ, a n * diffPow 0 s ((n : ℝ) + 1) =
        μ₁ * diffPow 0 s 1 + μ₂ * diffPow 1 s 1 + μ₃ * diffPow 2 s 1 +
          ∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1) := by
  obtain ⟨b₁, μ₁, p₁, z₁, n₁, m₁, e₁⟩ := abel_step q hq a 1 hp h0 hM
  obtain ⟨b₂, μ₂, p₂, z₂, n₂, m₂, e₂⟩ := abel_step q hq b₁ _ p₁ z₁ n₁
  obtain ⟨b₃, μ₃, -, -, n₃, m₃, e₃⟩ := abel_step q hq b₂ _ p₂ z₂ n₂
  refine ⟨b₃, μ₁, μ₂, μ₃, fun n => (n₃ n).trans_eq (by ring), m₁.trans_eq (by ring),
    m₂.trans_eq (by ring), m₃.trans_eq (by ring), fun s hs => ?_⟩
  have hd : ∀ (k n : ℕ), diffPow k s ((n : ℝ) + 1) - diffPow k s (((n + 1 : ℕ) : ℝ) + 1)
      = diffPow (k + 1) s ((n : ℝ) + 1) := by
    intro k n
    simp only [diffPow]; push_cast; rfl
  have hsum : ∀ k : ℕ, Summable (fun n : ℕ => ‖diffPow k s ((n : ℝ) + 1)‖) := fun k =>
    summable_diffPow k s (by have : (0 : ℝ) ≤ k := by positivity
                             linarith)
  have f₁ := e₁ _ (hsum 0)
  have f₂ := e₂ _ (hsum 1)
  have f₃ := e₃ _ (hsum 2)
  simp only [hd] at f₁ f₂ f₃
  simp only [Nat.cast_zero, zero_add] at f₁ f₂ f₃
  rw [f₁, f₂, f₃]
  ring

/- English proof (translation)
Use `(summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (show -t < -1 by linarith))` as an intermediate fact. Simplify using `using this`.
-/
theorem summable_nine_pow_mul_inv_sq_succ (t : ℝ) (ht : 1 < t) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-t)) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
    (show -t < -1 by linarith))
  simpa using this

/- English proof (translation)
Establish `hK : 0 ≤ K` using `(norm_nonneg _).trans (hb 0)`. Establish `h1` using `norm_diffPow_le 3 s ((n : ℝ) + 1) (by positivity) (by push_cast; linarith)`. Establish `h2 : ((n : ℝ) + 1) ^ (-(s.re + (3 : ℕ))) ≤ ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ))` using `Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by push_cast; linarith)`. Establish `hR0 : 0 ≤ R` using `(norm_nonneg _).trans hR`. Rewrite using `[norm_mul, mul_assoc]`.

Use `mul_le_mul (hb n) (h1.trans ?_) (norm_nonneg _) hK` and prove the remaining obligations. Use `mul_le_mul ?_ h2 (by positivity) (by positivity)` and prove the remaining obligations. Use `push_cast`. Use `gcongr`.
-/
theorem norm_term_le (b : ℕ → ℂ) (K R : ℝ) (hb : ∀ n, ‖b n‖ ≤ K) (s : ℂ)
    (hs : -(15 / 8 : ℝ) ≤ s.re) (hR : ‖s‖ ≤ R) (n : ℕ) :
    ‖b n * diffPow 3 s ((n : ℝ) + 1)‖ ≤ K * (R + 3) ^ 3 * ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hb 0)
  have h1 := norm_diffPow_le 3 s ((n : ℝ) + 1) (by positivity) (by push_cast; linarith)
  have h2 : ((n : ℝ) + 1) ^ (-(s.re + (3 : ℕ))) ≤ ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (by push_cast; linarith)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  rw [norm_mul, mul_assoc]
  refine mul_le_mul (hb n) (h1.trans ?_) (norm_nonneg _) hK
  refine mul_le_mul ?_ h2 (by positivity) (by positivity)
  push_cast
  gcongr

/- English proof (translation)
Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Establish `hz : ∑ n ∈ Finset.range q, χ (n : ZMod q) = 0`. Rewrite using `[← MulChar.sum_eq_zero_of_ne_one hχ]`. Use `Finset.sum_bij' (fun n _ => (n : ZMod q)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Introduce `x _`. Simplify using `using ZMod.val_lt x`. Introduce `n hn`. Conclude with `ZMod.val_cast_of_lt (Finset.mem_range.mp hn)`. Introduce `x _`.

Simplify using the standard rewrite rules. Introduce `n _`. Both sides reduce to the same expression. Establish `hz' : ∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q) = 0`. Establish `h1` using `Finset.sum_range_succ' (fun n : ℕ => χ (n : ZMod q)) q`.

Rewrite `h1` using `[Finset.sum_range_succ, hz]`. Simplify using `only [CharP.cast_eq_zero, Nat.cast_zero, zero_add] at h1`. Conclude with `(add_eq_right.mp h1.symm)`. Take `⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, he⟩` from `abel_three q hq (fun n => χ ((n + 1 : ℕ) : ZMod q)) (fun n => by simp) hz' (fun n => χ.norm_le_one _)`. Use `⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, fun s hs => ?_⟩` and prove the remaining obligations.

Use `set R : ℝ := ‖s‖ + 3 with hR`. Use `set U : Set ℂ := {z | -(15 / 8 : ℝ) < z.re} ∩ Metric.ball 0 R with hU`. Establish `hUo : IsOpen U` using `(isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball`. Establish `hUc : IsPreconnected U` using `((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected`. Establish `hsU : s ∈ U` using `⟨hs, by simp [hR]⟩`.

Establish `h2U : (2 : ℂ) ∈ U` using `⟨by simp; norm_num, by`. Simplify using `only [hR, Metric.mem_ball, dist_zero_right, Complex.norm_ofNat]`. Combine the linear relations using `[norm_nonneg s]⟩`. Establish `d1 : DifferentiableOn ℂ (fun z => ∑' n : ℕ, b n * diffPow 3 z ((n : ℝ) + 1)) U`. Use `Complex.differentiableOn_tsum_of_summable_norm ((summable_nine_pow_mul_inv_sq_succ (9 / 8) (by norm_num)).mul_left (8 * (q : ℝ) ^ 3 * (R + 3) ^ 3)) (fun n => ((differentiable_diffPow 3 _ (by positivity)).const_mul _).differentiableOn) hUo (fun n z hz => norm_term_le b _ R hb z (l …` and prove the remaining obligations.

Use `hz.2` as an intermediate fact. Simplify using `only [Metric.mem_ball, dist_zero_right] at this`. Conclude with `this.le`. Establish `d2 : DifferentiableOn ℂ (fun z => μ₁ * diffPow 0 z 1 + μ₂ * diffPow 1 z 1 + μ₃ * diffPow 2 z 1 + ∑' n : ℕ, b n * diffPow 3 z ((n : ℝ) + 1)) U` using `(((((differentiable_diffPow 0 1 one_pos).const_mul _).add ((differentiable_diffPow 1 1 one_pos).const_mul _)).add ((differentiable_diffPow 2 1 one_pos).const_mul _)).differentiableOn).add d1`. Establish `d3 : DifferentiableOn ℂ (LFunction χ) U` using `(differentiable_LFunction hχ).differentiableOn`.

Use `(d3.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (d2.analyticOnNhd hUo) hUc h2U ?_ hsU` and prove the remaining obligations. Establish `hV : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ)` using `(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)`. Use `filter_upwards [hV] with z hz1`. Establish `hz1' : 1 < z.re` using `hz1`. Rewrite using `[← he z hz1', LFunction_eq_LSeries χ hz1', LSeries, (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz1').tsum_eq_zero_add]`.

Simplify using `only [LSeries.term_zero, zero_add]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[LSeries.term_of_ne_zero (Nat.succ_ne_zero n), diffPow, cpow_neg, div_eq_mul_inv]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem LFunction_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ (b : ℕ → ℂ) (μ₁ μ₂ μ₃ : ℂ), (∀ n, ‖b n‖ ≤ 8 * (q : ℝ) ^ 3) ∧ ‖μ₁‖ ≤ q ∧
      ‖μ₂‖ ≤ 2 * (q : ℝ) ^ 2 ∧ ‖μ₃‖ ≤ 4 * (q : ℝ) ^ 3 ∧
      ∀ s : ℂ, -(15 / 8 : ℝ) < s.re → LFunction χ s =
        μ₁ * diffPow 0 s 1 + μ₂ * diffPow 1 s 1 + μ₃ * diffPow 2 s 1 +
          ∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hz : ∑ n ∈ Finset.range q, χ (n : ZMod q) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one hχ]
    refine Finset.sum_bij' (fun n _ => (n : ZMod q)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro x _; simpa using ZMod.val_lt x
    · intro n hn; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
    · intro x _; simp
    · intro n _; rfl
  have hz' : ∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q) = 0 := by
    have h1 := Finset.sum_range_succ' (fun n : ℕ => χ (n : ZMod q)) q
    rw [Finset.sum_range_succ, hz] at h1
    simp only [CharP.cast_eq_zero, Nat.cast_zero, zero_add] at h1
    exact (add_eq_right.mp h1.symm)
  obtain ⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, he⟩ := abel_three q hq
    (fun n => χ ((n + 1 : ℕ) : ZMod q)) (fun n => by simp) hz' (fun n => χ.norm_le_one _)
  refine ⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, fun s hs => ?_⟩
  set R : ℝ := ‖s‖ + 3 with hR
  set U : Set ℂ := {z | -(15 / 8 : ℝ) < z.re} ∩ Metric.ball 0 R with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hsU : s ∈ U := ⟨hs, by simp [hR]⟩
  have h2U : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by
    simp only [hR, Metric.mem_ball, dist_zero_right, Complex.norm_ofNat]
    linarith [norm_nonneg s]⟩
  have d1 : DifferentiableOn ℂ (fun z => ∑' n : ℕ, b n * diffPow 3 z ((n : ℝ) + 1)) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_nine_pow_mul_inv_sq_succ (9 / 8) (by norm_num)).mul_left (8 * (q : ℝ) ^ 3 * (R + 3) ^ 3))
      (fun n => ((differentiable_diffPow 3 _ (by positivity)).const_mul _).differentiableOn)
      hUo (fun n z hz => norm_term_le b _ R hb z (le_of_lt hz.1) ?_ n)
    have := hz.2
    simp only [Metric.mem_ball, dist_zero_right] at this
    exact this.le
  have d2 : DifferentiableOn ℂ (fun z => μ₁ * diffPow 0 z 1 + μ₂ * diffPow 1 z 1 +
      μ₃ * diffPow 2 z 1 + ∑' n : ℕ, b n * diffPow 3 z ((n : ℝ) + 1)) U :=
    (((((differentiable_diffPow 0 1 one_pos).const_mul _).add
      ((differentiable_diffPow 1 1 one_pos).const_mul _)).add
      ((differentiable_diffPow 2 1 one_pos).const_mul _)).differentiableOn).add d1
  have d3 : DifferentiableOn ℂ (LFunction χ) U := (differentiable_LFunction hχ).differentiableOn
  refine (d3.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (d2.analyticOnNhd hUo)
    hUc h2U ?_ hsU
  have hV : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  filter_upwards [hV] with z hz1
  have hz1' : 1 < z.re := hz1
  rw [← he z hz1', LFunction_eq_LSeries χ hz1', LSeries,
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz1').tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), diffPow, cpow_neg, div_eq_mul_inv]
  push_cast
  rfl

end LLeft

open LLeft in

/- English proof (translation)
Use `set Z : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) with hZ`. Establish `hZ0 : 0 ≤ Z` using `tsum_nonneg fun n => by positivity`. Use `⟨15 + 64 * Z, by positivity, fun q _ χ hχ s hs => ?_⟩` and prove the remaining obligations. Take `⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, he⟩` from `LFunction_eq q χ hχ`. Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)`.

Establish `hn` using `norm_nonneg s`. Use `set A : ℝ := (q : ℝ) ^ 4 with hA`. Use `set B : ℝ := (‖s‖ + 2) ^ 4 with hB`. Establish `q1 : (q : ℝ) ≤ A` using `by simpa using pow_le_pow_right₀ hq (show 1 ≤ 4 by norm_num)`. Establish `q2 : (q : ℝ) ^ 2 ≤ A` using `pow_le_pow_right₀ hq (by norm_num)`.

Establish `q3 : (q : ℝ) ^ 3 ≤ A` using `pow_le_pow_right₀ hq (by norm_num)`. Establish `hA0 : 0 ≤ A` using `by positivity`. Establish `hs1 : 1 ≤ ‖s‖ + 2` using `by linarith`. Establish `b0 : 1 ≤ B` using `one_le_pow₀ hs1`. Establish `b2 : (‖s‖ + 2) ^ 2 ≤ B` using `pow_le_pow_right₀ hs1 (by norm_num)`.

Establish `b3 : (‖s‖ + 3) ^ 3 ≤ 8 * B`. Combine the equalities or inequalities in the displayed calculation. Establish `t0 : ‖diffPow 0 s 1‖ ≤ B` using `by simpa [diffPow] using b0`. Establish `t1 : ‖diffPow 1 s 1‖ ≤ 5 * B`. Establish `h1 : ‖diffPow 0 s 1‖ ≤ 1` using `by simp [diffPow]`.

Establish `h2 : ‖diffPow 0 s (1 + 1)‖ ≤ 4`. Rewrite using `[diffPow, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[diffPow]`. Combine the linear relations using `[norm_sub_le (diffPow 0 s 1) (diffPow 0 s (1 + 1))]`.

Establish `t2 : ‖diffPow 2 s 1‖ ≤ B`. Use `norm_diffPow_le 2 s 1 one_pos (by push_cast; linarith)` as an intermediate fact. Simplify using `only [Real.one_rpow, mul_one, Nat.cast_ofNat] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t3 : ‖∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1)‖ ≤ 8 * (q : ℝ) ^ 3 * (‖s‖ + 3) ^ 3 * Z`.

Rewrite using `[hZ, ← tsum_mul_left]`. Conclude with `tsum_of_norm_bounded ((summable_nine_pow_mul_inv_sq_succ (9 / 8) (by norm_num)).mul_left _).hasSum fun n => norm_term_le b _ _ hb s (by linarith) le_rfl n`. Establish `u0 : ‖μ₁ * diffPow 0 s 1‖ ≤ A * B`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (m₁.trans q1) t0 (norm_nonneg _) hA0`.

Establish `u1 : ‖μ₂ * diffPow 1 s 1‖ ≤ (2 * A) * (5 * B)`. Rewrite using `[norm_mul]; exact mul_le_mul (by linarith) t1 (norm_nonneg _) (by positivity)`. Establish `u2 : ‖μ₃ * diffPow 2 s 1‖ ≤ (4 * A) * B`. Rewrite using `[norm_mul]; exact mul_le_mul (by linarith) t2 (norm_nonneg _) (by positivity)`. Establish `u3 : 8 * (q : ℝ) ^ 3 * (‖s‖ + 3) ^ 3 * Z ≤ 8 * A * (8 * B) * Z` using `by gcongr`.

Rewrite using `[he s (by linarith)]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Use `norm_add₃_le (a := μ₁ * diffPow 0 s 1) (b := μ₂ * diffPow 1 s 1) (c := μ₃ * diffPow 2 s 1)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_LFunction_le_poly_left :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ,
      -(7/4 : ℝ) ≤ s.re → ‖LFunction χ s‖ ≤ C * (q : ℝ) ^ 4 * (‖s‖ + 2) ^ 4 := by
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  refine ⟨15 + 64 * Z, by positivity, fun q _ χ hχ s hs => ?_⟩
  obtain ⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, he⟩ := LFunction_eq q χ hχ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hn := norm_nonneg s
  set A : ℝ := (q : ℝ) ^ 4 with hA
  set B : ℝ := (‖s‖ + 2) ^ 4 with hB
  have q1 : (q : ℝ) ≤ A := by simpa using pow_le_pow_right₀ hq (show 1 ≤ 4 by norm_num)
  have q2 : (q : ℝ) ^ 2 ≤ A := pow_le_pow_right₀ hq (by norm_num)
  have q3 : (q : ℝ) ^ 3 ≤ A := pow_le_pow_right₀ hq (by norm_num)
  have hA0 : 0 ≤ A := by positivity
  have hs1 : 1 ≤ ‖s‖ + 2 := by linarith
  have b0 : 1 ≤ B := one_le_pow₀ hs1
  have b2 : (‖s‖ + 2) ^ 2 ≤ B := pow_le_pow_right₀ hs1 (by norm_num)
  have b3 : (‖s‖ + 3) ^ 3 ≤ 8 * B := by
    calc (‖s‖ + 3) ^ 3 ≤ (2 * (‖s‖ + 2)) ^ 3 := by gcongr; linarith
      _ = 8 * (‖s‖ + 2) ^ 3 := by ring
      _ ≤ 8 * B := by gcongr; exact pow_le_pow_right₀ hs1 (by norm_num)
  have t0 : ‖diffPow 0 s 1‖ ≤ B := by simpa [diffPow] using b0
  have t1 : ‖diffPow 1 s 1‖ ≤ 5 * B := by
    have h1 : ‖diffPow 0 s 1‖ ≤ 1 := by simp [diffPow]
    have h2 : ‖diffPow 0 s (1 + 1)‖ ≤ 4 := by
      rw [diffPow, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      calc ((1 : ℝ) + 1) ^ (-s).re ≤ (1 + 1) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simp only [neg_re]; linarith)
        _ = 4 := by norm_num
    rw [diffPow]
    linarith [norm_sub_le (diffPow 0 s 1) (diffPow 0 s (1 + 1))]
  have t2 : ‖diffPow 2 s 1‖ ≤ B := by
    have := norm_diffPow_le 2 s 1 one_pos (by push_cast; linarith)
    simp only [Real.one_rpow, mul_one, Nat.cast_ofNat] at this
    linarith
  have t3 : ‖∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1)‖ ≤ 8 * (q : ℝ) ^ 3 * (‖s‖ + 3) ^ 3 * Z := by
    rw [hZ, ← tsum_mul_left]
    exact tsum_of_norm_bounded ((summable_nine_pow_mul_inv_sq_succ (9 / 8) (by norm_num)).mul_left _).hasSum
      fun n => norm_term_le b _ _ hb s (by linarith) le_rfl n
  have u0 : ‖μ₁ * diffPow 0 s 1‖ ≤ A * B := by
    rw [norm_mul]; exact mul_le_mul (m₁.trans q1) t0 (norm_nonneg _) hA0
  have u1 : ‖μ₂ * diffPow 1 s 1‖ ≤ (2 * A) * (5 * B) := by
    rw [norm_mul]; exact mul_le_mul (by linarith) t1 (norm_nonneg _) (by positivity)
  have u2 : ‖μ₃ * diffPow 2 s 1‖ ≤ (4 * A) * B := by
    rw [norm_mul]; exact mul_le_mul (by linarith) t2 (norm_nonneg _) (by positivity)
  have u3 : 8 * (q : ℝ) ^ 3 * (‖s‖ + 3) ^ 3 * Z ≤ 8 * A * (8 * B) * Z := by gcongr
  rw [he s (by linarith)]
  refine (norm_add_le _ _).trans ?_
  have := norm_add₃_le (a := μ₁ * diffPow 0 s 1) (b := μ₂ * diffPow 1 s 1)
    (c := μ₃ * diffPow 2 s 1)
  nlinarith

end GlobalTheory
