import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

/- English proof (translation)
Introduce `D j w`. Establish `hq : 1 ≤ D.host.q` using `by have := D.host.qd_big.1; omega`. Establish `hd : 1 ≤ D.host.d` using `by have := D.host.qd_big.2; omega`. Establish `hqR : (1 : ℝ) ≤ D.host.q` using `by exact_mod_cast hq`. Establish `hdR : (1 : ℝ) ≤ D.host.d` using `by exact_mod_cast hd`.

Establish `hlq : 0 ≤ Real.log D.host.q` using `Real.log_nonneg hqR`. Establish `hld : 0 ≤ Real.log D.host.d` using `Real.log_nonneg hdR`. Establish `hQ : (1 : ℝ) ≤ D.host.QS` using `by exact_mod_cast D.host.QS_pos`. Establish `hl2 : 0 ≤ Real.log D.host.QS` using `Real.log_nonneg hQ`. Establish `hQf : (D.host.QS : ℝ) ≤ 4 * ((D.R.f : ℝ) / 2) ^ 2`.

Establish `h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2` using `by exact_mod_cast D.host.QS_le`. Establish `h2 : (D.R.f : ℝ) = 2 * D.R.n` using `by unfold Ranks.f; push_cast; ring`. Rewrite using `[h2]`. Use polynomial arithmetic with `[sq_nonneg (D.R.n : ℝ)]`. Establish `hlf : Real.log D.host.QS ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2)` using `Real.log_le_log (by linarith) hQf`.

Establish `hlog : Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) = Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) + Real.log D.host.q + Real.log D.host.d`. Establish `h0 : (0 : ℝ) < 4 * ((D.R.f : ℝ) / 2) ^ 2` using `by linarith`. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul h0.ne' (by positivity)]`. Establish `hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ)` using `Nat.cast_nonneg _`. Use `⟨hq, hd, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hlog]`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `h0 : (1 : ℝ) ≤ D.host.g 0` using `by exact_mod_cast (D.host.g_prime 0).one_le`. Establish `h1 : (1 : ℝ) ≤ D.host.g 1` using `by exact_mod_cast (D.host.g_prime 1).one_le`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hc2 : (c2 D w : ℝ) = (WeightAlgebra.DF w : ℝ)` using `rfl`. Establish `hch : (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) ≤ (WeightAlgebra.DF w : ℝ) + 1`. Establish `h1` using `(Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) / 2 by positivity)).le`. Unfold `Formalism.MainNotions.DIV.Cons.cHalf`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `a1` using `mul_le_mul_of_nonneg_left hlf hD`. Establish `a2` using `mul_le_mul_of_nonneg_right hch hlq`. Establish `a3` using `mul_le_mul_of_nonneg_right hch hld`. Rewrite using `[hlog, hc2]`.

Use the polynomial consequences of the given equalities and inequalities. Introduce `a b c`. Establish `hQ0 : 0 < D.host.QS` using `D.host.QS_pos`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `pPow`.

Conclude with `Nat.one_le_iff_ne_zero.mpr (by positivity)`. Unfold `pPow`. Use `push_cast`. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]`.
-/
theorem pPow_size : ∀ (D : D7) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ D.host.q ∧ 1 ≤ D.host.d ∧ 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ∧ (c2 D w : ℝ) * Real.log D.host.QS + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.q + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.d ≤ ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ ∀ a b c : ℕ, 1 ≤ pPow D a b c ∧ Real.log (pPow D a b c) = a * Real.log D.host.QS + b * Real.log D.host.q + c * Real.log D.host.d := by
  intro D j w
  have hq : 1 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hqR : (1 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have hdR : (1 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have hlq : 0 ≤ Real.log D.host.q := Real.log_nonneg hqR
  have hld : 0 ≤ Real.log D.host.d := Real.log_nonneg hdR
  have hQ : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hl2 : 0 ≤ Real.log D.host.QS := Real.log_nonneg hQ
  have hQf : (D.host.QS : ℝ) ≤ 4 * ((D.R.f : ℝ) / 2) ^ 2 := by
    have h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
    have h2 : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
    rw [h2]; nlinarith [sq_nonneg (D.R.n : ℝ)]
  have hlf : Real.log D.host.QS ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) := Real.log_le_log (by linarith) hQf
  have hlog : Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) =
      Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) + Real.log D.host.q + Real.log D.host.d := by
    have h0 : (0 : ℝ) < 4 * ((D.R.f : ℝ) / 2) ^ 2 := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul h0.ne' (by positivity)]
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  refine ⟨hq, hd, ?_, ?_, ?_, ?_⟩
  · rw [hlog]; linarith
  · apply Real.log_nonneg
    have h0 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_le
    have h1 : (1 : ℝ) ≤ D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).one_le
    nlinarith
  · have hc2 : (c2 D w : ℝ) = (WeightAlgebra.DF w : ℝ) := rfl
    have hch : (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) ≤ (WeightAlgebra.DF w : ℝ) + 1 := by
      have h1 := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) / 2 by positivity)).le
      unfold Formalism.MainNotions.DIV.Cons.cHalf
      linarith
    have a1 := mul_le_mul_of_nonneg_left hlf hD
    have a2 := mul_le_mul_of_nonneg_right hch hlq
    have a3 := mul_le_mul_of_nonneg_right hch hld
    rw [hlog, hc2]
    nlinarith
  · intro a b c
    have hQ0 : 0 < D.host.QS := D.host.QS_pos
    refine ⟨?_, ?_⟩
    · unfold pPow
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · unfold pPow
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]

end GlobalTheory.RunIn
