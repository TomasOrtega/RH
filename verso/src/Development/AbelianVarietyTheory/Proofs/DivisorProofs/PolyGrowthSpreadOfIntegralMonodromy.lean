import Mathlib
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `hS : 0 ≤ ∑ j, ∑ i, ‖M j i‖` using `Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _`. Use `(pi_norm_le_iff_of_nonneg (mul_nonneg hS (norm_nonneg x))).2 fun j => ?_` and prove the remaining obligations. Rewrite using `[h j]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma intMatrix_smul_sum_norm_le {m g : ℕ} (M : Fin m → Fin m → ℤ) (x y : Fin m → Fin g → ℂ)
    (h : ∀ j, y j = ∑ i, M j i • x i) :
    ‖y‖ ≤ (∑ j, ∑ i, ‖M j i‖) * ‖x‖ := by
  have hS : 0 ≤ ∑ j, ∑ i, ‖M j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hS (norm_nonneg x))).2 fun j => ?_
  rw [h j]
  calc ‖∑ i, M j i • x i‖ ≤ ∑ i, ‖M j i • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖M j i‖ * ‖x‖ := Finset.sum_le_sum fun i _ =>
        (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _))
    _ = (∑ i, ‖M j i‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j, ∑ i, ‖M j i‖) * ‖x‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun j => ∑ i, ‖M j i‖)
          (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ j)) (norm_nonneg x)

/- English proof (translation)
Introduce `g m lam C k P Q h1 h2 h3 R`. Use `set τ : ℂ := 2 * Real.pi * Complex.I with hτ`. Establish `hτre : τ.re = 0` using `by simp [hτ]`. Establish `hτim : τ.im = 2 * Real.pi` using `by simp [hτ]`. Establish `hτn : ‖τ‖ = 2 * Real.pi` using `by simp [hτ, abs_of_pos Real.pi_pos]`.

Establish `hexp : ∀ s, Complex.exp (s + τ) = Complex.exp s`. Introduce `s`. Rewrite using `[Complex.exp_add, hτ, Complex.exp_two_pi_mul_I, mul_one]`. Establish `hSP : 0 ≤ ∑ j, ∑ i, ‖P j i‖` using `Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _`. Establish `hSQ : 0 ≤ ∑ j, ∑ i, ‖Q j i‖` using `Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _`.

Use `set A : ℝ := 1 + ∑ j, ∑ i, ‖P j i‖ + ∑ j, ∑ i, ‖Q j i‖ with hA`. Establish `hA1 : 1 ≤ A` using `by linarith`. Establish `hPA : ∀ s : ℂ, s.re < 0 → ‖lam (s + τ)‖ ≤ A * ‖lam s‖` using `fun s hs => (intMatrix_smul_sum_norm_le P _ _ (h1 s hs)).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))`. Establish `hQA : ∀ s : ℂ, s.re < 0 → ‖lam s‖ ≤ A * ‖lam (s + τ)‖` using `fun s hs => (intMatrix_smul_sum_norm_le Q _ _ (h2 s hs)).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))`. Use `set B : ℝ := A * (1 + 2 * Real.pi) ^ k with hB`.

Establish `hB1 : 1 ≤ B` using `one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ (by linarith [Real.pi_pos]))`. Establish `hgrow : ∀ s t : ℂ, ‖t‖ ≤ ‖s‖ + 2 * Real.pi → (1 + ‖t‖) ^ k ≤ (1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k`. Introduce `s t h`. Rewrite using `[← mul_pow]`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises.

Use polynomial arithmetic with `[norm_nonneg s, Real.pi_pos]`. Establish `hM : 0 ≤ max C 0` using `le_max_right _ _`. Establish `key : ∀ n : ℕ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi + 2 * Real.pi * n → ‖lam s‖ ≤ max C 0 * B ^ n * (1 + ‖s‖) ^ k`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `s hs he hi`. Establish `hX : 0 ≤ (1 + ‖s‖) ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_zero, mul_one]`.

Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) hX`. Consider the case `succ n ih`. Introduce `s hs he hi`. Establish `hX : 0 ≤ (1 + ‖s‖) ^ k` using `by positivity`. Establish `hBn : 1 ≤ B ^ (n + 1)` using `one_le_pow₀ hB1`.

Distinguish the cases in `hsm : |s.im| ≤ Real.pi`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ hX` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Use `push_neg at hsm`.

Establish `hn0 : (0 : ℝ) ≤ 2 * Real.pi * n` using `by positivity`. Establish `hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1` using `by push_cast; ring`. Rewrite `hi` using `[hcast]`. Take `⟨hi1, hi2⟩` from `abs_le.mp hi`. Choose the witnesses or unpack the hypotheses as in `⟨t, hlt, htre, hte, htn, hti⟩ : ∃ t : ℂ, ‖lam s‖ ≤ A * ‖lam t‖ ∧ t.re = s.re ∧ Complex.exp t = Complex.exp s ∧ ‖t‖ ≤ ‖s‖ + 2 * Real.pi ∧ |t.im| ≤ Real.pi + 2 * Real.pi * n := by`.

Break down `lt_abs.mp hsm with hpos | hneg` into its components or cases. Use `⟨s - τ, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hPA (s - τ) (by simp [Complex.sub_re, hτre, hs])` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Simplify using `[hτre]`.

Use `hexp (s - τ)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this.symm`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rw [Complex.sub_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]`.

Use `⟨s + τ, hQA s hs, ?_, hexp s, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hτre]`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `rw [Complex.add_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]`. Establish `hIH` using `ih t (by rw [htre]; exact hs) (by rw [hte]; exact he) hti`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨max C 0 * B ^ ⌈R / (2 * Real.pi)⌉₊, fun s hs he hi => key _ s hs he (hi.trans ?_)⟩` and prove the remaining obligations. Establish `hc : R / (2 * Real.pi) ≤ (⌈R / (2 * Real.pi)⌉₊ : ℝ)` using `Nat.le_ceil _`. Rewrite `hc` using `[div_le_iff₀ (by positivity)]`. Combine the linear relations using `[Real.pi_pos]`.
-/
theorem polyGrowth_spread_of_integral_monodromy : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ) (P Q : Fin m → Fin m → ℤ), (∀ s : ℂ, s.re < 0 → ∀ j, lam (s + 2 * Real.pi * Complex.I) j = ∑ i, P j i • lam s i) → (∀ s : ℂ, s.re < 0 → ∀ j, lam s j = ∑ i, Q j i • lam (s + 2 * Real.pi * Complex.I) i) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  intro g m lam C k P Q h1 h2 h3 R
  set τ : ℂ := 2 * Real.pi * Complex.I with hτ
  have hτre : τ.re = 0 := by simp [hτ]
  have hτim : τ.im = 2 * Real.pi := by simp [hτ]
  have hτn : ‖τ‖ = 2 * Real.pi := by simp [hτ, abs_of_pos Real.pi_pos]
  have hexp : ∀ s, Complex.exp (s + τ) = Complex.exp s := by
    intro s; rw [Complex.exp_add, hτ, Complex.exp_two_pi_mul_I, mul_one]
  have hSP : 0 ≤ ∑ j, ∑ i, ‖P j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hSQ : 0 ≤ ∑ j, ∑ i, ‖Q j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  set A : ℝ := 1 + ∑ j, ∑ i, ‖P j i‖ + ∑ j, ∑ i, ‖Q j i‖ with hA
  have hA1 : 1 ≤ A := by linarith
  have hPA : ∀ s : ℂ, s.re < 0 → ‖lam (s + τ)‖ ≤ A * ‖lam s‖ := fun s hs =>
    (intMatrix_smul_sum_norm_le P _ _ (h1 s hs)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hQA : ∀ s : ℂ, s.re < 0 → ‖lam s‖ ≤ A * ‖lam (s + τ)‖ := fun s hs =>
    (intMatrix_smul_sum_norm_le Q _ _ (h2 s hs)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  set B : ℝ := A * (1 + 2 * Real.pi) ^ k with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ (by linarith [Real.pi_pos]))
  have hgrow : ∀ s t : ℂ, ‖t‖ ≤ ‖s‖ + 2 * Real.pi →
      (1 + ‖t‖) ^ k ≤ (1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k := by
    intro s t h
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [norm_nonneg s, Real.pi_pos]
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have key : ∀ n : ℕ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 →
      |s.im| ≤ Real.pi + 2 * Real.pi * n → ‖lam s‖ ≤ max C 0 * B ^ n * (1 + ‖s‖) ^ k := by
    intro n
    induction n with
    | zero =>
      intro s hs he hi
      have hX : 0 ≤ (1 + ‖s‖) ^ k := by positivity
      calc ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := h3 s hs he (by simpa using hi)
        _ ≤ max C 0 * B ^ 0 * (1 + ‖s‖) ^ k := by
          rw [pow_zero, mul_one]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    | succ n ih =>
      intro s hs he hi
      have hX : 0 ≤ (1 + ‖s‖) ^ k := by positivity
      have hBn : 1 ≤ B ^ (n + 1) := one_le_pow₀ hB1
      by_cases hsm : |s.im| ≤ Real.pi
      · calc ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := h3 s hs he hsm
          _ ≤ max C 0 * B ^ (n + 1) * (1 + ‖s‖) ^ k := by
            apply mul_le_mul_of_nonneg_right _ hX
            calc C ≤ max C 0 := le_max_left _ _
              _ = max C 0 * 1 := (mul_one _).symm
              _ ≤ max C 0 * B ^ (n + 1) := mul_le_mul_of_nonneg_left hBn hM
      · push_neg at hsm
        have hn0 : (0 : ℝ) ≤ 2 * Real.pi * n := by positivity
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hi
        obtain ⟨hi1, hi2⟩ := abs_le.mp hi
        obtain ⟨t, hlt, htre, hte, htn, hti⟩ : ∃ t : ℂ, ‖lam s‖ ≤ A * ‖lam t‖ ∧ t.re = s.re ∧
            Complex.exp t = Complex.exp s ∧ ‖t‖ ≤ ‖s‖ + 2 * Real.pi ∧
            |t.im| ≤ Real.pi + 2 * Real.pi * n := by
          rcases lt_abs.mp hsm with hpos | hneg
          · refine ⟨s - τ, ?_, ?_, ?_, ?_, ?_⟩
            · have := hPA (s - τ) (by simp [Complex.sub_re, hτre, hs])
              rwa [sub_add_cancel] at this
            · simp [hτre]
            · have := hexp (s - τ); rw [sub_add_cancel] at this; exact this.symm
            · calc ‖s - τ‖ ≤ ‖s‖ + ‖τ‖ := norm_sub_le _ _
                _ = ‖s‖ + 2 * Real.pi := by rw [hτn]
            · rw [Complex.sub_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]
          · refine ⟨s + τ, hQA s hs, ?_, hexp s, ?_, ?_⟩
            · simp [hτre]
            · calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
                _ = ‖s‖ + 2 * Real.pi := by rw [hτn]
            · rw [Complex.add_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]
        have hIH := ih t (by rw [htre]; exact hs) (by rw [hte]; exact he) hti
        calc ‖lam s‖ ≤ A * ‖lam t‖ := hlt
          _ ≤ A * (max C 0 * B ^ n * (1 + ‖t‖) ^ k) :=
            mul_le_mul_of_nonneg_left hIH (by linarith)
          _ ≤ A * (max C 0 * B ^ n * ((1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hgrow s t htn)
                (mul_nonneg hM (pow_nonneg (by linarith) n))) (by linarith)
          _ = max C 0 * B ^ (n + 1) * (1 + ‖s‖) ^ k := by rw [hB]; ring
  refine ⟨max C 0 * B ^ ⌈R / (2 * Real.pi)⌉₊, fun s hs he hi => key _ s hs he (hi.trans ?_)⟩
  have hc : R / (2 * Real.pi) ≤ (⌈R / (2 * Real.pi)⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ (by positivity)] at hc
  linarith [Real.pi_pos]

end GlobalTheory
