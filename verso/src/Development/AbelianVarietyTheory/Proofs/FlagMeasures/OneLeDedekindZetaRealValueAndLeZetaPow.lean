import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DedekindZetaBound

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Establish `: l ≠ 0` using `by omega`. Simplify using `[this]`. Rewrite using `[LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem term_eq_ofReal (a : ℕ → ℕ) {l : ℕ} (hl : 2 ≤ l) (n : ℕ) :
    LSeries.term (fun n => (a n : ℂ)) (l : ℂ) n = (((a n : ℝ) * ((n : ℝ) ^ l)⁻¹ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : l ≠ 0 := by omega
    simp [this]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv]
    push_cast
    rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `hasSum_single (f := LSeries.term (fun n => (((ArithmeticFunction.zeta ^ 0 : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s) 1 (fun b hb => by` as an intermediate fact. Break down `eq_or_ne b 0 with rfl | h0` into its components or cases. Simplify using the standard rewrite rules.

Simplify using `[LSeries.term_of_ne_zero h0, ArithmeticFunction.one_apply_ne hb])`. Simplify `this` using `[LSeriesHasSum]`. Consider the case `succ k ih`. Use `ArithmeticFunction.LSeriesHasSum_mul (f := ((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) (g := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) ih (ArithmeticFunction.LSeriesHasSum_zeta hs)` as an intermediate fact. Rewrite `this` using `[← ArithmeticFunction.natCoe_mul]`.

Rewrite using `[pow_succ, pow_succ]`. Conclude with `this`.
-/
theorem lseriesHasSum_zeta_pow {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    LSeriesHasSum (fun n => (((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s
      (riemannZeta s ^ k) := by
  induction k with
  | zero =>
    have := hasSum_single (f := LSeries.term
      (fun n => (((ArithmeticFunction.zeta ^ 0 : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s) 1
      (fun b hb => by
        rcases eq_or_ne b 0 with rfl | h0
        · simp
        · simp [LSeries.term_of_ne_zero h0, ArithmeticFunction.one_apply_ne hb])
    simpa [LSeriesHasSum] using this
  | succ k ih =>
    have := ArithmeticFunction.LSeriesHasSum_mul
      (f := ((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      (g := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      ih (ArithmeticFunction.LSeriesHasSum_zeta hs)
    rw [← ArithmeticFunction.natCoe_mul] at this
    rw [pow_succ, pow_succ]
    exact this

/- English proof (translation)
Establish `hs : 1 < ((l : ℂ)).re`. Rewrite using `[Complex.natCast_re]`. Conclude with `hl` after adjusting the coercions. Establish `h` using `lseriesHasSum_zeta_pow hs k`. Establish `e : riemannZeta (l : ℂ) = ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l : ℝ) : ℂ)`.

Rewrite using `[zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.ofReal_tsum]`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Rewrite using `[Complex.cpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite `h` using `[e, ← Complex.ofReal_pow, LSeriesHasSum, funext (term_eq_ofReal _ hl)]`. Conclude with `Complex.hasSum_ofReal.1 h`.
-/
theorem hasSum_zeta_pow {l : ℕ} (hl : 2 ≤ l) (k : ℕ) :
    HasSum (fun n : ℕ => (((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) *
      ((n : ℝ) ^ l)⁻¹) ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ k) := by
  have hs : 1 < ((l : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hl
  have h := lseriesHasSum_zeta_pow hs k
  have e : riemannZeta (l : ℂ) = ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    rw [Complex.cpow_natCast]
    push_cast
    rfl
  rw [e, ← Complex.ofReal_pow, LSeriesHasSum, funext (term_eq_ofReal _ hl)] at h
  exact Complex.hasSum_ofReal.1 h

/- English proof (translation)
Introduce `E _ _ l hl`. Establish `h` using `hasSum_zeta_pow hl (Module.finrank ℚ E)`. Use `set a : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹ with ha`. Establish `h0 : ∀ n, 0 ≤ a n` using `fun n => by positivity`. Establish `hle : ∀ n : ℕ, a n ≤ (((ArithmeticFunction.zeta ^ Module.finrank ℚ E : ArithmeticFunction ℕ) n : ℕ) : ℝ) * ((n : ℝ) ^ l)⁻¹` using `fun n => by`.

Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Establish `: l ≠ 0` using `by omega`. Simplify using `[ha, this]`. Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Conclude with `GlobalTheory.ncard_ideal_absNorm_eq_le E hn` after adjusting the coercions.

Establish `hsum : Summable a` using `Summable.of_nonneg_of_le h0 hle h.summable`. Establish `e : zetaE E l = ∑' n, a n`. Unfold `zetaE dedekindZeta LSeries`. Rewrite using `[funext (term_eq_ofReal _ hl), ← Complex.ofReal_tsum, Complex.ofReal_re]`. Rewrite using `[e]`.

Use `⟨le_trans ?_ (hsum.le_tsum 1 fun n _ => h0 n), hasSum_le hle hsum.hasSum h⟩` and prove the remaining obligations. Simplify using `[ha, Ideal.absNorm_eq_one_iff]`.
-/
theorem one_le_zetaE_and_le : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), 2 ≤ l →
    1 ≤ zetaE E l ∧ zetaE E l ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ Module.finrank ℚ E := by
  intro E _ _ l hl
  have h := hasSum_zeta_pow hl (Module.finrank ℚ E)
  set a : ℕ → ℝ := fun n =>
    (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹ with ha
  have h0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have hle : ∀ n : ℕ, a n ≤
      (((ArithmeticFunction.zeta ^ Module.finrank ℚ E : ArithmeticFunction ℕ) n : ℕ) : ℝ) *
        ((n : ℝ) ^ l)⁻¹ := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · have : l ≠ 0 := by omega
      simp [ha, this]
    · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast GlobalTheory.ncard_ideal_absNorm_eq_le E hn
  have hsum : Summable a := Summable.of_nonneg_of_le h0 hle h.summable
  have e : zetaE E l = ∑' n, a n := by
    unfold zetaE dedekindZeta LSeries
    rw [funext (term_eq_ofReal _ hl), ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [e]
  refine ⟨le_trans ?_ (hsum.le_tsum 1 fun n _ => h0 n), hasSum_le hle hsum.hasSum h⟩
  simp [ha, Ideal.absNorm_eq_one_iff]

end GlobalTheory.DedekindZetaBound
