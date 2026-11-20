import Mathlib

namespace GlobalTheory.UnitNormRealPartBound

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Separate the alternatives or extract the components of the hypothesis.

Extract witnesses or component facts from the available result. Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
lemma norm_eq_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) : ‖z‖ = 1 := by
  have hup : ∀ n : ℕ, ‖z‖ ^ n < 3 / 2 := fun n => by
    have := h n
    calc ‖z‖ ^ n = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel, norm_pow]
      _ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 3 / 2 := by rw [norm_one]; linarith
  have hlo : ∀ n : ℕ, 1 / 2 < ‖z‖ ^ n := fun n => by
    have := h n
    have h2 : ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ + ‖z ^ n‖ := by
      calc ‖(1 : ℂ)‖ = ‖-(z ^ n - 1) + z ^ n‖ := by ring_nf
        _ ≤ ‖-(z ^ n - 1)‖ + ‖z ^ n‖ := norm_add_le _ _
        _ = ‖z ^ n - 1‖ + ‖z ^ n‖ := by rw [norm_neg]
    rw [norm_one, norm_pow] at h2
    linarith
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) h1
    linarith [hlo n]
  · exact h1
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) h1
    linarith [hup n]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma re_gt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1 / 2) : 7 / 8 < w.re := by
  have h1 : ‖w - 1‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (w - 1)]
  have h2 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1 h2
  simp at h1
  nlinarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities. Simplify using the standard rewrite rules.
-/
theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have hz := norm_eq_one h
  have hnp : ∀ n : ℕ, ‖z ^ n‖ = 1 := fun n => by rw [norm_pow, hz, one_pow]
  have hre : ∀ n : ℕ, 7 / 8 < (z ^ n).re := fun n => re_gt (hnp n) (h n)
  have key : ∀ k : ℕ, (7 / 4 : ℝ) ^ k * |z.im| ≤ |(z ^ (2 ^ k)).im| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = z ^ (2 ^ k) * z ^ (2 ^ k) := by
        rw [pow_succ, pow_mul, sq]
      have hr := hre (2 ^ k)
      have e2 : (z ^ (2 ^ (k + 1))).im = 2 * (z ^ (2 ^ k)).re * (z ^ (2 ^ k)).im := by
        rw [e, Complex.mul_im]; ring
      rw [e2, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * (z ^ 2 ^ k).re), pow_succ]
      have : (7 / 4 : ℝ) ≤ 2 * (z ^ 2 ^ k).re := by linarith
      have hn : 0 ≤ (7 / 4 : ℝ) ^ k * |z.im| := by positivity
      nlinarith [abs_nonneg (z ^ 2 ^ k).im]
  have him : z.im = 0 := by
    by_contra hne
    have hpos : 0 < |z.im| := abs_pos.mpr hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / |z.im|) (by norm_num : (1 : ℝ) < 7 / 4)
    have hb : |(z ^ (2 ^ k)).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (hnp _).le
    have : 1 < (7 / 4 : ℝ) ^ k * |z.im| := by rwa [div_lt_iff₀ hpos] at hk
    linarith [key k]
  have h1 := hre 1
  rw [pow_one] at h1
  have h2 : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him] at h2
  apply Complex.ext
  · simp; nlinarith
  · simp [him]

end GlobalTheory.UnitNormRealPartBound
