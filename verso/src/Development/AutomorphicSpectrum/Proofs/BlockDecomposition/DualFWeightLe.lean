import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Parseval

/- English proof (translation)
Establish `hm : 0 < q ^ 2 + s ^ 2`. Break down `eq_or_ne q 0 with hq | hq` into its components or cases. Break down `eq_or_ne s 0 with hs | hs` into its components or cases. Conclude with `absurd (by rw [hD, hq, hs]; ring) hD0`. Check the signs of the components of the expression.

Check the signs of the components of the expression. Take `⟨m, hmdef⟩ : ∃ m, m = q ^ 2 + s ^ 2` from `⟨_, rfl⟩`. Take `⟨l, hldef⟩ : ∃ l, l = (p * q + r * s) / (q ^ 2 + s ^ 2)` from `⟨_, rfl⟩`. Rewrite using `[← hldef, ← hmdef]`. Rewrite `hm` using `[← hmdef]`.

Take `⟨t, htdef⟩ : ∃ t, t = |ζ - l| / (|D| / Real.sqrt m)` from `⟨_, rfl⟩`. Rewrite using `[← htdef]`. Establish `ht0 : 0 ≤ t` using `by rw [htdef]; positivity`. Establish `hD2 : 0 < D ^ 2` using `by positivity`. Establish `ht2 : t ^ 2 = (ζ - l) ^ 2 * m / D ^ 2`.

Rewrite using `[htdef, div_pow, div_pow, sq_abs, sq_abs, Real.sq_sqrt hm.le]`. Clear the denominators using the available nonvanishing facts. Establish `hid : (s * ζ - r) ^ 2 + (p - q * ζ) ^ 2 = m * (ζ - l) ^ 2 + D ^ 2 / m`. Rewrite using `[hldef, ← hmdef]`. Establish `hm' : m ≠ 0` using `hm.ne'`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hD, hmdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx : ((s * ζ - r) / D) ^ 2 ≤ N ^ 2` using `sq_le_sq.2 (by rwa [abs_of_nonneg hN])`. Establish `hy : ((p - q * ζ) / D) ^ 2 ≤ N ^ 2` using `sq_le_sq.2 (by rwa [abs_of_nonneg hN])`.

Establish `hsum : ((s * ζ - r) / D) ^ 2 + ((p - q * ζ) / D) ^ 2 = t ^ 2 + 1 / m`. Rewrite using `[div_pow, div_pow, ← add_div, hid, ht2]`. Clear the denominators using the available nonvanishing facts. Establish `hinv : 0 < 1 / m` using `by positivity`. Establish `ht4 : t ^ 2 ≤ 2 * N ^ 2` using `by linarith`.

Establish `ht : t ≤ 2 * N`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use the polynomial consequences of the given equalities and inequalities. Establish `hle : (1 + t) ^ 2 ≤ 4 * (1 + N) ^ 2` using `by nlinarith`.

Rewrite using `[← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma geom_real (p q r s ζ N D : ℝ) (hD : D = p * s - q * r) (hD0 : D ≠ 0) (hN : 0 ≤ N)
    (h0 : |(s * ζ - r) / D| ≤ N) (h1 : |(p - q * ζ) / D| ≤ N) :
    ((1 + N) ^ 2)⁻¹ ≤ 4 * ((1 + |ζ - (p * q + r * s) / (q ^ 2 + s ^ 2)| /
      (|D| / Real.sqrt (q ^ 2 + s ^ 2))) ^ 2)⁻¹ := by
  have hm : 0 < q ^ 2 + s ^ 2 := by
    rcases eq_or_ne q 0 with hq | hq
    · rcases eq_or_ne s 0 with hs | hs
      · exact absurd (by rw [hD, hq, hs]; ring) hD0
      · positivity
    · positivity
  obtain ⟨m, hmdef⟩ : ∃ m, m = q ^ 2 + s ^ 2 := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l, l = (p * q + r * s) / (q ^ 2 + s ^ 2) := ⟨_, rfl⟩
  rw [← hldef, ← hmdef]
  rw [← hmdef] at hm
  obtain ⟨t, htdef⟩ : ∃ t, t = |ζ - l| / (|D| / Real.sqrt m) := ⟨_, rfl⟩
  rw [← htdef]
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hD2 : 0 < D ^ 2 := by positivity
  have ht2 : t ^ 2 = (ζ - l) ^ 2 * m / D ^ 2 := by
    rw [htdef, div_pow, div_pow, sq_abs, sq_abs, Real.sq_sqrt hm.le]
    field_simp
  have hid : (s * ζ - r) ^ 2 + (p - q * ζ) ^ 2 = m * (ζ - l) ^ 2 + D ^ 2 / m := by
    rw [hldef, ← hmdef]
    have hm' : m ≠ 0 := hm.ne'
    field_simp
    rw [hD, hmdef]
    ring
  have hx : ((s * ζ - r) / D) ^ 2 ≤ N ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hN])
  have hy : ((p - q * ζ) / D) ^ 2 ≤ N ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hN])
  have hsum : ((s * ζ - r) / D) ^ 2 + ((p - q * ζ) / D) ^ 2 = t ^ 2 + 1 / m := by
    rw [div_pow, div_pow, ← add_div, hid, ht2]
    field_simp
  have hinv : 0 < 1 / m := by positivity
  have ht4 : t ^ 2 ≤ 2 * N ^ 2 := by linarith
  have ht : t ≤ 2 * N := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hle : (1 + t) ^ 2 ≤ 4 * (1 + N) ^ 2 := by nlinarith
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/- English proof (translation)
Introduce `h ζ hD`. Establish `hdet : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0`. Rewrite using `[Matrix.det_fin_two]`. Both sides reduce to the same expression. Establish `h0` using `norm_le_pi_norm (dualF h ζ) 0`.

Establish `h1` using `norm_le_pi_norm (dualF h ζ) 1`. Rewrite `h0`, `h1` using `[Real.norm_eq_abs]`. Conclude with `geom_real (h 0 0) (h 0 1) (h 1 0) (h 1 1) ζ _ _ hdet hD (norm_nonneg _) h0 h1`.
-/
theorem dualF_weight_le : ∀ (h : Ad3.LR.M22) (ζ : ℝ), (Matrix.of h).det ≠ 0 →
    ((1 + ‖GlobalTheory.CompanionTheory.Parseval.dualF h ζ‖) ^ 2)⁻¹ ≤ 4 * GlobalTheory.CompanionTheory.Parseval.wt
      (|(Matrix.of h).det| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2))
      ((h 0 0 * h 0 1 + h 1 0 * h 1 1) / (h 0 1 ^ 2 + h 1 1 ^ 2)) ζ := by
  intro h ζ hD
  have hdet : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [Matrix.det_fin_two]
    rfl
  have h0 := norm_le_pi_norm (dualF h ζ) 0
  have h1 := norm_le_pi_norm (dualF h ζ) 1
  rw [Real.norm_eq_abs] at h0 h1
  exact geom_real (h 0 0) (h 0 1) (h 1 0) (h 1 1) ζ _ _ hdet hD (norm_nonneg _) h0 h1

end GlobalTheory.CompanionTheory.Parseval
