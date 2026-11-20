import Mathlib

namespace GlobalTheory.UnitNormRealPartBound

/- English proof (translation)
Establish `hup : ∀ n : ℕ, ‖z‖ ^ n < 3 / 2` using `fun n => by`. Use `h n` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hlo : ∀ n : ℕ, 1 / 2 < ‖z‖ ^ n` using `fun n => by`. Use `h n` as an intermediate fact.

Establish `h2 : ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ + ‖z ^ n‖`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h2` using `[norm_one, norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `lt_trichotomy ‖z‖ 1 with h1 | h1 | h1` into its components or cases.

Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) h1`. Combine the linear relations using `[hlo n]`. Conclude with `h1`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (3 / 2 : ℝ) h1`. Combine the linear relations using `[hup n]`.
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
Establish `h1 : ‖w - 1‖ ^ 2 < 1 / 4` using `by nlinarith [norm_nonneg (w - 1)]`. Establish `h2 : ‖w‖ ^ 2 = 1` using `by rw [hw]; norm_num`. Rewrite `h1`, `h2` using `[← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`. Simplify using `at h1`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma re_gt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1 / 2) : 7 / 8 < w.re := by
  have h1 : ‖w - 1‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (w - 1)]
  have h2 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1 h2
  simp at h1
  nlinarith

/- English proof (translation)
Introduce `z h`. Establish `hz` using `norm_eq_one h`. Establish `hnp : ∀ n : ℕ, ‖z ^ n‖ = 1` using `fun n => by rw [norm_pow, hz, one_pow]`. Establish `hre : ∀ n : ℕ, 7 / 8 < (z ^ n).re` using `fun n => re_gt (hnp n) (h n)`. Establish `key : ∀ k : ℕ, (7 / 4 : ℝ) ^ k * |z.im| ≤ |(z ^ (2 ^ k)).im|`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : z ^ (2 ^ (k + 1)) = z ^ (2 ^ k) * z ^ (2 ^ k)`.

Rewrite using `[pow_succ, pow_mul, sq]`. Establish `hr` using `hre (2 ^ k)`. Establish `e2 : (z ^ (2 ^ (k + 1))).im = 2 * (z ^ (2 ^ k)).re * (z ^ (2 ^ k)).im`. Rewrite using `[e, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * (z ^ 2 ^ k).re), pow_succ]`. Establish `: (7 / 4 : ℝ) ≤ 2 * (z ^ 2 ^ k).re` using `by linarith`. Establish `hn : 0 ≤ (7 / 4 : ℝ) ^ k * |z.im|` using `by positivity`. Use polynomial arithmetic with `[abs_nonneg (z ^ 2 ^ k).im]`. Establish `him : z.im = 0`.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < |z.im|` using `abs_pos.mpr hne`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (1 / |z.im|) (by norm_num : (1 : ℝ) < 7 / 4)`. Establish `hb : |(z ^ (2 ^ k)).im| ≤ 1` using `(Complex.abs_im_le_norm _).trans (hnp _).le`. Establish `: 1 < (7 / 4 : ℝ) ^ k * |z.im|` using `by rwa [div_lt_iff₀ hpos] at hk`.

Combine the linear relations using `[key k]`. Establish `h1` using `hre 1`. Rewrite `h1` using `[pow_one]`. Establish `h2 : ‖z‖ ^ 2 = 1` using `by rw [hz]; norm_num`. Rewrite `h2` using `[← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities. Simplify using `[him]`.
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
