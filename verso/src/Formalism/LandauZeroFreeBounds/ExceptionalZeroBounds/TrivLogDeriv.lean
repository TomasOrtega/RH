import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.EulerFactorLogDerivBound
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Take `⟨K, hK0, hK⟩` from `zeta_neg_log_deriv_re_bound`. Use `⟨K + 1, fun q _ σ t hσ hσ2 => ?_⟩` and prove the remaining obligations. Establish `hs : 1 < ((σ : ℂ) + t * I).re` using `by simpa using hσ`. Establish `h1` using `re_negLogDeriv_le q ((σ : ℂ) + t * I) hs`. Establish `h2` using `hK σ t hσ hσ2`.

Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `hlq : 0 ≤ Real.log q` using `Real.log_nonneg hq`. Establish `hT : 0 ≤ Real.log (|t| + 2)` using `Real.log_nonneg (by linarith [abs_nonneg t])`. Establish `hlog : Real.log ((q : ℝ) * (|t| + 2)) = Real.log q + Real.log (|t| + 2)` using `Real.log_mul (by linarith : (0 : ℝ) < q).ne' (by linarith [abs_nonneg t] : (0 : ℝ) < |t| + 2).ne'`. Rewrite using `[hlog]`.

Use polynomial arithmetic with `[mul_nonneg hK0 hlq]`.
-/
theorem trivial_log_deriv_bound : TrivLogDeriv := by
  obtain ⟨K, hK0, hK⟩ := zeta_neg_log_deriv_re_bound
  refine ⟨K + 1, fun q _ σ t hσ hσ2 => ?_⟩
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h1 := re_negLogDeriv_le q ((σ : ℂ) + t * I) hs
  have h2 := hK σ t hσ hσ2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog : Real.log ((q : ℝ) * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith : (0 : ℝ) < q).ne' (by linarith [abs_nonneg t] : (0 : ℝ) < |t| + 2).ne'
  rw [hlog]
  nlinarith [mul_nonneg hK0 hlq]

end Formalism.ZeroFreeDirichlet
