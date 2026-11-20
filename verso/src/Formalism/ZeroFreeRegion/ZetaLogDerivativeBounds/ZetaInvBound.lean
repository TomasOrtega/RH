import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Filter Topology LSeries ArithmeticFunction

noncomputable section

namespace Formalism.ZF

namespace MoebiusInverseZetaBounds

/- English proof (translation)
Establish `h` using `(summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)`. Simplify `h` using `only [Nat.cast_add, Nat.cast_one]`.
-/
lemma summable_shift {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa only [Nat.cast_add, Nat.cast_one] using h

/- English proof (translation)
Establish `ha : 0 < x + 1` using `by linarith`. Establish `hy : 0 < x / (x + 1)` using `div_pos hx ha`. Establish `hlog : Real.log (x / (x + 1)) ≤ x / (x + 1) - 1` using `Real.log_le_sub_one_of_pos hy`. Establish `hexp : 1 + σ / (x + 1) ≤ (x / (x + 1)) ^ (-σ)`. Rewrite using `[Real.rpow_def_of_pos hy]`.

Establish `h1` using `Real.add_one_le_exp (Real.log (x / (x + 1)) * (-σ))`. Establish `h2 : σ / (x + 1) ≤ Real.log (x / (x + 1)) * (-σ)`. Establish `e : σ / (x + 1) = (x / (x + 1) - 1) * (-σ)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonpos_right hlog (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA` using `Real.rpow_pos_of_pos ha (-σ)`. Establish `hsplit : x ^ (-σ) = (x + 1) ^ (-σ) * (x / (x + 1)) ^ (-σ)`.

Rewrite using `[Real.div_rpow hx.le ha.le]`. Clear the denominators using the available nonvanishing facts. Establish `hm1 : (x + 1) ^ (-σ - 1) = (x + 1) ^ (-σ) / (x + 1)`. Rewrite using `[Real.rpow_sub ha, Real.rpow_one]`. Rewrite using `[le_div_iff₀ hσ, hm1, hsplit]`.

Establish `hmul : (x + 1) ^ (-σ) * (σ / (x + 1)) ≤ (x + 1) ^ (-σ) * ((x / (x + 1)) ^ (-σ) - 1)` using `mul_le_mul_of_nonneg_left (by linarith) hA.le`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma rpow_le_integral {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) :
    (x + 1) ^ (-σ - 1) ≤ (x ^ (-σ) - (x + 1) ^ (-σ)) / σ := by
  have ha : 0 < x + 1 := by linarith
  have hy : 0 < x / (x + 1) := div_pos hx ha
  have hlog : Real.log (x / (x + 1)) ≤ x / (x + 1) - 1 := Real.log_le_sub_one_of_pos hy
  have hexp : 1 + σ / (x + 1) ≤ (x / (x + 1)) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hy]
    have h1 := Real.add_one_le_exp (Real.log (x / (x + 1)) * (-σ))
    have h2 : σ / (x + 1) ≤ Real.log (x / (x + 1)) * (-σ) := by
      have e : σ / (x + 1) = (x / (x + 1) - 1) * (-σ) := by
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonpos_right hlog (by linarith)
    linarith
  have hA := Real.rpow_pos_of_pos ha (-σ)
  have hsplit : x ^ (-σ) = (x + 1) ^ (-σ) * (x / (x + 1)) ^ (-σ) := by
    rw [Real.div_rpow hx.le ha.le]
    field_simp
  have hm1 : (x + 1) ^ (-σ - 1) = (x + 1) ^ (-σ) / (x + 1) := by
    rw [Real.rpow_sub ha, Real.rpow_one]
  rw [le_div_iff₀ hσ, hm1, hsplit]
  have hmul : (x + 1) ^ (-σ) * (σ / (x + 1)) ≤ (x + 1) ^ (-σ) * ((x / (x + 1)) ^ (-σ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hA.le
  calc (x + 1) ^ (-σ) / (x + 1) * σ = (x + 1) ^ (-σ) * (σ / (x + 1)) := by ring
    _ ≤ (x + 1) ^ (-σ) * ((x / (x + 1)) ^ (-σ) - 1) := hmul
    _ = (x + 1) ^ (-σ) * (x / (x + 1)) ^ (-σ) - (x + 1) ^ (-σ) := by ring

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + (1 - ((n : ℝ) + 1) ^ (-σ)) / σ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[Finset.sum_range_succ]`. Establish `h` using `rpow_le_integral (x := (k : ℝ) + 1) (by positivity) hσ`. Establish `e : (1 - ((k : ℝ) + 1) ^ (-σ)) / σ + (((k : ℝ) + 1) ^ (-σ) - ((k : ℝ) + 1 + 1) ^ (-σ)) / σ = (1 - ((k : ℝ) + 1 + 1) ^ (-σ)) / σ` using `by ring`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `Real.tsum_le_of_sum_range_le (fun n => by positivity)` to reduce the goal to its premises. Introduce `n`. Consider the cases of `n with`. Consider the case `zero`. Simplify using `only [Finset.range_zero, Finset.sum_empty]`.

Establish `: 0 < 1 / σ` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ k`. Establish `h1` using `key k`. Establish `h2 : 0 ≤ ((k : ℝ) + 1) ^ (-σ)` using `by positivity`.

Establish `h3 : (1 - ((k : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ` using `div_le_div_of_nonneg_right (by linarith) hσ.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma tsum_rpow_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ := by
  have key : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + (1 - ((n : ℝ) + 1) ^ (-σ)) / σ := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have h := rpow_le_integral (x := (k : ℝ) + 1) (by positivity) hσ
      have e : (1 - ((k : ℝ) + 1) ^ (-σ)) / σ + (((k : ℝ) + 1) ^ (-σ) - ((k : ℝ) + 1 + 1) ^ (-σ)) / σ =
          (1 - ((k : ℝ) + 1 + 1) ^ (-σ)) / σ := by ring
      push_cast
      linarith
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro n
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have : 0 < 1 / σ := by positivity
    linarith
  | succ k =>
    have h1 := key k
    have h2 : 0 ≤ ((k : ℝ) + 1) ^ (-σ) := by positivity
    have h3 : (1 - ((k : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ := div_le_div_of_nonneg_right (by linarith) hσ.le
    linarith

/- English proof (translation)
Rewrite using `[LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]`. Simplify using `only [Pi.one_apply, norm_one]`. Use `push_cast`. Rewrite using `[show -(s.re - 1) - 1 = -s.re by ring, Real.rpow_neg (by positivity), one_div]`.
-/
lemma norm_term_one_succ (s : ℂ) (n : ℕ) :
    ‖term (1 : ℕ → ℂ) s (n + 1)‖ = ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := by
  rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
  simp only [Pi.one_apply, norm_one]
  push_cast
  rw [show -(s.re - 1) - 1 = -s.re by ring, Real.rpow_neg (by positivity), one_div]

/- English proof (translation)
Use `LSeries.norm_term_le s ?_` and prove the remaining obligations. Simplify using `only [Pi.one_apply, norm_one]`. Rewrite using `[Complex.norm_intCast]`. Conclude with `ArithmeticFunction.abs_moebius_le_one` after adjusting the coercions.
-/
lemma norm_term_moebius_le (s : ℂ) (n : ℕ) :
    ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  refine LSeries.norm_term_le s ?_
  simp only [Pi.one_apply, norm_one]
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

end MoebiusInverseZetaBounds

open MoebiusInverseZetaBounds in
/- English proof (translation)
Introduce `s hs`. Establish `hL` using `LSeries_one_mul_Lseries_moebius hs`. Rewrite `hL` using `[LSeries_one_eq_riemannZeta hs]`. Establish `hinv` using `eq_inv_of_mul_eq_one_right hL`. Rewrite using `[← norm_inv, ← hinv]`.

Establish `hσ : 0 < s.re - 1` using `by linarith`. Establish `hsum1 : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1)` using `summable_shift (by linarith)`. Establish `hs1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖`. Rewrite using `[← summable_nat_add_iff 1]`. Simplify `hsum1` using `only [norm_term_one_succ]`.

Establish `hsμ : Summable fun n => ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖` using `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_moebius_le s) hs1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hs1.tsum_eq_zero_add]`. Simplify using `only [LSeries.term_zero, norm_zero, zero_add, norm_term_one_succ]`. Use `_ ≤ 1 + 1 / (s.re - 1) := tsum_rpow_le hσ`.

Use `_ = s.re / (s.re - 1) := by`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zetaInvBound_statement : ZetaInvBound := by
  intro s hs
  have hL := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hL
  have hinv := eq_inv_of_mul_eq_one_right hL
  rw [← norm_inv, ← hinv]
  have hσ : 0 < s.re - 1 := by linarith
  have hsum1 : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := summable_shift (by linarith)
  have hs1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ := by
    rw [← summable_nat_add_iff 1]
    simpa only [norm_term_one_succ] using hsum1
  have hsμ : Summable fun n => ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_moebius_le s) hs1
  calc ‖LSeries (fun n => ((moebius n : ℤ) : ℂ)) s‖
      ≤ ∑' n, ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsμ
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ := Summable.tsum_le_tsum (norm_term_moebius_le s) hsμ hs1
    _ = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := by
      rw [hs1.tsum_eq_zero_add]
      simp only [LSeries.term_zero, norm_zero, zero_add, norm_term_one_succ]
    _ ≤ 1 + 1 / (s.re - 1) := tsum_rpow_le hσ
    _ = s.re / (s.re - 1) := by
      field_simp
      ring

end Formalism.ZF
