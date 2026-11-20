import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

def lamF (σ : ℝ) : ℝ := ∑' n, ‖term ↗Λ (σ : ℂ) n‖

/- English proof (translation)
Establish `hL` using `LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs`. Establish `hsum : Summable fun n => ‖term ↗Λ s n‖` using `summable_norm_iff.2 (LSeriesSummable_vonMangoldt hs)`. Establish `heq : (fun n => ‖term ↗Λ s n‖) = fun n => ‖term ↗Λ ((s.re : ℝ) : ℂ) n‖`. Use function extensionality and compare the values at `n`. Rewrite using `[norm_term_eq, norm_term_eq]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_logDeriv_le_lamF {s : ℂ} (hs : 1 < s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ lamF s.re := by
  have hL := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsum : Summable fun n => ‖term ↗Λ s n‖ := summable_norm_iff.2 (LSeriesSummable_vonMangoldt hs)
  have heq : (fun n => ‖term ↗Λ s n‖) = fun n => ‖term ↗Λ ((s.re : ℝ) : ℂ) n‖ := by
    funext n
    rw [norm_term_eq, norm_term_eq]
    simp
  calc ‖deriv riemannZeta s / riemannZeta s‖ = ‖L ↗Λ s‖ := by rw [hL, neg_div, norm_neg]
    _ ≤ ∑' n, ‖term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
    _ = lamF s.re := by rw [heq]; rfl

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `h : term ↗Λ (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ)`. Rewrite using `[term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]`. Rewrite using `[h, Complex.norm_real, Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]`.
-/
lemma term_vonMangoldt_real (σ : ℝ) (n : ℕ) :
    term ↗Λ (σ : ℂ) n = ((‖term ↗Λ (σ : ℂ) n‖ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h : term ↗Λ (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
        Complex.ofReal_natCast]
    rw [h, Complex.norm_real, Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]

/- English proof (translation)
Establish `h : L ↗Λ (σ : ℂ) = ((lamF σ : ℝ) : ℂ)`. Rewrite using `[LSeries, lamF, Complex.ofReal_tsum]`. Conclude with `tsum_congr fun n => term_vonMangoldt_real σ n`. Rewrite using `[h, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ lamF σ from tsum_nonneg fun n => norm_nonneg _)]`.
-/
lemma lamF_eq_norm {σ : ℝ} (hσ : 1 < σ) : lamF σ = ‖L ↗Λ (σ : ℂ)‖ := by
  have h : L ↗Λ (σ : ℂ) = ((lamF σ : ℝ) : ℂ) := by
    rw [LSeries, lamF, Complex.ofReal_tsum]
    exact tsum_congr fun n => term_vonMangoldt_real σ n
  rw [h, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ lamF σ from tsum_nonneg fun n => norm_nonneg _)]

/- English proof (translation)
Establish `hs : ∀ x : ℝ, 1 < x → Summable fun n => ‖term ↗Λ (x : ℂ) n‖` using `fun x hx => summable_norm_iff.2 (LSeriesSummable_vonMangoldt (by simpa using hx))`. Unfold `lamF`. Use `Summable.tsum_le_tsum (fun n => ?_) (hs τ (by linarith)) (hs σ hσ)` and prove the remaining obligations. Rewrite using `[norm_term_eq, norm_term_eq]`. Use `split_ifs with hn`.

Both sides reduce to the same expression. Simplify using `only [ofReal_re]`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn`. Conclude with `div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_le_rpow_of_exponent_le hn1 h)`.
-/
lemma lamF_anti {σ τ : ℝ} (hσ : 1 < σ) (h : σ ≤ τ) : lamF τ ≤ lamF σ := by
  have hs : ∀ x : ℝ, 1 < x → Summable fun n => ‖term ↗Λ (x : ℂ) n‖ := fun x hx =>
    summable_norm_iff.2 (LSeriesSummable_vonMangoldt (by simpa using hx))
  unfold lamF
  refine Summable.tsum_le_tsum (fun n => ?_) (hs τ (by linarith)) (hs σ hσ)
  rw [norm_term_eq, norm_term_eq]
  split_ifs with hn
  · rfl
  · simp only [ofReal_re]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 h)

end Formalism.ZF
