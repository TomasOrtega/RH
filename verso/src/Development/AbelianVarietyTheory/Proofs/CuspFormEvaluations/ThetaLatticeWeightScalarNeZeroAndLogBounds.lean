import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormNormaliserEqHalfDegreeLogStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBoundsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

/- English proof (translation)
Take `⟨hnn, hlog⟩` from `GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ`. Establish `hp` using `((GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w).2.2.2.2.2 (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)).1`. Establish `hσ : σ (sOf B hinj EX w : B.KO) = σ (nnW B hinj EX w : B.KO) * (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℂ)`. Unfold `sOf`. Use `push_cast`.

Rewrite using `[map_mul, map_natCast]`. Establish `hne : σ (nnW B hinj EX w : B.KO) ≠ 0`. Rewrite using `[map_ne_zero]`. Conclude with `hnn` after adjusting the coercions. Establish `hpne : ((pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℕ) : ℝ) ≠ 0`.

Establish `: 0 < pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)` using `hp`. Check the signs of the components of the expression. Rewrite using `[hσ, norm_mul, Complex.norm_natCast, Real.log_mul (norm_ne_zero_iff.mpr hne) hpne, hlog]`.
-/
private theorem log_norm_sOf_eq_DF_log_add_log_pPow (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (sOf B hinj EX w : B.KO)‖ =
      (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
        Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) := by
  obtain ⟨hnn, hlog⟩ := GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ
  have hp := ((GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w).2.2.2.2.2 (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)).1
  have hσ : σ (sOf B hinj EX w : B.KO) = σ (nnW B hinj EX w : B.KO) *
      (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℂ) := by
    unfold sOf
    push_cast
    rw [map_mul, map_natCast]
  have hne : σ (nnW B hinj EX w : B.KO) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hnn
  have hpne : ((pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℕ) : ℝ) ≠ 0 := by
    have : 0 < pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) := hp
    positivity
  rw [hσ, norm_mul, Complex.norm_natCast, Real.log_mul (norm_ne_zero_iff.mpr hne) hpne, hlog]

/- English proof (translation)
Introduce `D B hinj EX j w`. Take `⟨_, _, hB0, hA0, hP, hpp⟩` from `GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w`. Take `⟨hp1, hplog⟩` from `hpp (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)`. Establish `hlp0 : 0 ≤ Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ)` using `Real.log_nonneg (by exact_mod_cast hp1)`. Establish `hlpB : Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) ≤ ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)`.

Rewrite using `[hplog]`. Conclude with `hP`. Establish `hDF : (0 : ℝ) ≤ WeightAlgebra.DF w` using `Nat.cast_nonneg _`. Establish `hsz : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size`. Establish `key : w.size = (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1`.

Unfold `WeightFamilies.Wt.size WeightAlgebra.DF WeightAlgebra.degP`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: (0 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ)`. Check the signs of the components of the expression.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqq : Real.log (qq D : ℝ) ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))`. Break down `Nat.eq_zero_or_pos (qq D) with h | h` into its components or cases. Rewrite using `[h, Nat.cast_zero, Real.log_zero]`. Conclude with `hA0`.

Establish `h0 : qq D ≤ D.host.g 0` using `min_le_left _ _`. Establish `h1 : qq D ≤ D.host.g 1` using `min_le_right _ _`. Establish `hle : qq D ≤ D.host.g 0 * D.host.g 1` using `h0.trans (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le h h1))`. Establish `hcast : (qq D : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)` using `by exact_mod_cast hle`. Conclude with `Real.log_le_log (by exact_mod_cast h) hcast`.

Use `⟨?_, fun σ => ?_⟩` and prove the remaining obligations. Unfold `sOf`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Take `⟨σ⟩ : Nonempty (B.KO →+* ℂ)` from `inferInstance`. Conclude with `(GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ).1`.

Establish `: pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) ≠ 0` using `by omega`. Conclude with `this` after adjusting the coercions. Rewrite using `[log_norm_sOf_eq_DF_log_add_log_pPow D B hinj EX j w σ]`. Establish `hA : (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D : ℝ) ≤ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))` using `mul_le_mul_of_nonneg_left hqq (by positivity)`. Establish `hA1 : 0 ≤ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))` using `by positivity`.

Establish `hL : lamStar D = Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) + Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)` using `rfl`. Use `⟨by linarith, by linarith, by linarith, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[mul_nonneg hDF hA0]`. Use `_ ≤ w.size * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) + Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) := mul_le_mul_of_nonneg_right hsz (by linarith)`.

Use `_ = lamStar D * w.size := by rw [hL]; ring`.
-/
theorem sOf_ne_zero_and_log_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j), sOf B hinj EX w ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, 0 ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ≤ lamStar D * w.size := by
  intro D B hinj EX j w
  obtain ⟨_, _, hB0, hA0, hP, hpp⟩ := GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w
  obtain ⟨hp1, hplog⟩ := hpp (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)
  have hlp0 : 0 ≤ Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hlpB : Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) ≤
      ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    rw [hplog]; exact hP
  have hDF : (0 : ℝ) ≤ WeightAlgebra.DF w := Nat.cast_nonneg _

  have hsz : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size := by
    have key : w.size = (WeightAlgebra.DF w : ℝ) +
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 := by
      unfold WeightFamilies.Wt.size WeightAlgebra.DF WeightAlgebra.degP
      push_cast
      ring
    have : (0 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      positivity
    linarith

  have hqq : Real.log (qq D : ℝ) ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rcases Nat.eq_zero_or_pos (qq D) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; exact hA0
    · have h0 : qq D ≤ D.host.g 0 := min_le_left _ _
      have h1 : qq D ≤ D.host.g 1 := min_le_right _ _
      have hle : qq D ≤ D.host.g 0 * D.host.g 1 :=
        h0.trans (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le h h1))
      have hcast : (qq D : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by exact_mod_cast hle
      exact Real.log_le_log (by exact_mod_cast h) hcast
  refine ⟨?_, fun σ => ?_⟩
  · unfold sOf
    refine mul_ne_zero ?_ ?_
    · obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
      exact (GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ).1
    · have : pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) ≠ 0 := by omega
      exact_mod_cast this
  · rw [log_norm_sOf_eq_DF_log_add_log_pPow D B hinj EX j w σ]
    have hA : (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D : ℝ) ≤
        (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hqq (by positivity)
    have hA1 : 0 ≤ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by positivity
    have hL : lamStar D = Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
        Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := rfl
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    calc (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
          Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ)
        ≤ ((WeightAlgebra.DF w : ℝ) + 1) * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
            Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) := by
          nlinarith [mul_nonneg hDF hA0]
      _ ≤ w.size * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
            Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) :=
          mul_le_mul_of_nonneg_right hsz (by linarith)
      _ = lamStar D * w.size := by rw [hL]; ring

end GlobalTheory.RunIn
