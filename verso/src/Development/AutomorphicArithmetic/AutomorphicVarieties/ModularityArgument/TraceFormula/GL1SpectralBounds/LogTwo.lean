import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed

open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne
open scoped ComplexConjugate

/- English proof (translation)
Introduce `hE W q X d A hS x`. Take `⟨F, hFa, hFe⟩` from `hE W q X d A hS x x`. Simplify using `only [if_true] at hFe`. Establish `hq : ∀ w, (0 : ℝ) < q w` using `fun w => by exact_mod_cast lt_of_lt_of_le two_pos (hS.primes.two w)`. Establish `hne : ∀ σ : ℝ, 1 < σ → (σ : ℂ) - 1 ≠ 0` using `fun σ h => sub_ne_zero.2 (by exact_mod_cast h.ne')`.

Establish `h1 : F 1 ≠ 0`. Introduce `h0`. Establish `hc : ContinuousOn (fun t : ℝ => dslope F 1 t) (Set.Icc 1 2)` using `fun t ht => by`. Use `(ContinuousAt.comp (g := dslope F 1) ?_ Complex.continuous_ofReal.continuousAt).continuousWithinAt` and prove the remaining obligations. Break down `eq_or_ne (t : ℂ) 1 with e | e` into its components or cases.

Rewrite using `[e]`. Conclude with `continuousAt_dslope_same.2 (by simpa using (hFa 1 one_pos).differentiableAt)`. Conclude with `(continuousAt_dslope_of_ne e).2 (hFa t (by linarith [ht.1])).continuousAt`. Take `⟨M, hM⟩` from `isCompact_Icc.exists_bound_of_continuousOn hc`. Use `dirichlet_series_unbounded landauL newton_identities_low_degree euler_product_log_bound removable_singularity_holds (convergence_of_landau_euler landauL euler_product_log_bound) W q X d A hS Unit (fun _ => x) ⟨M, fun σ a b => ?_⟩` and prove the remaining obligations.

Establish `e1 : ∀ p, lterm q (A x) (A x) σ p = ((DirichletSeriesUnbounded₂.cc A (fun _ : Unit => x) p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)) : ℝ) : ℂ)` using `fun p => by simpa using DirichletSeriesUnbounded₂.sum_lterm q A (fun _ : Unit => x) hq σ p`. Establish `e2` using `sub_smul_dslope F 1 (σ : ℂ)`. Rewrite `e2` using `[h0, sub_zero, hFe σ a, smul_eq_mul]`. Establish `e3` using `hM σ ⟨a.le, b⟩`. Simplify using `only [mul_left_cancel₀ (hne σ a) e2, Complex.norm_exp] at e3`.

Simplify using `only [Finset.univ_unique, Finset.sum_singleton]`. Simplify using `only [e1, ← Complex.ofReal_tsum, Complex.ofReal_re] at e3 ⊢`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun p => mul_nonneg (DirichletSeriesUnbounded₂.cc_nonneg A _ p) (Real.exp_pos _).le)]`. Conclude with `le_trans (by linarith [Real.add_one_le_exp (∑' p, DirichletSeriesUnbounded₂.cc A (fun _ : Unit => x) p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)))]) e3`. Establish `h2 : ∀ t ∈ Set.Icc (1 : ℝ) 2, F t ≠ 0` using `fun t ht => by`.

Break down `ht.1.eq_or_lt with e | e` into its components or cases. Rewrite using `[← e]`. Simplify using `using h1`. Rewrite using `[hFe t e]`. Conclude with `mul_ne_zero (hne t e) (Complex.exp_ne_zero _)`.

Establish `hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2)` using `fun t ht => (((hFa t (by linarith [ht.1])).continuousAt.comp Complex.continuous_ofReal.continuousAt).norm.log (norm_ne_zero_iff.2 (h2 t ht))).continuousWithinAt`. Take `⟨M, hM⟩` from `isCompact_Icc.exists_bound_of_continuousOn hc`. Use `⟨M, fun σ a b => ?_⟩` and prove the remaining obligations. Establish `h3` using `hM σ ⟨a.le, b⟩`. Establish `hn : ‖(σ : ℂ) - 1‖ = σ - 1`.

Rewrite using `[← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`. Rewrite `h3` using `[hFe σ a, norm_mul, hn, Complex.norm_exp, Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, Real.norm_eq_abs, add_comm]`. Conclude with `h3`.
-/
theorem UpperTheory.V.Z.Tf.GOne.logTwo :
    ExtId → LogTwo := by
  intro hE W q X d A hS x
  obtain ⟨F, hFa, hFe⟩ := hE W q X d A hS x x
  simp only [if_true] at hFe
  have hq : ∀ w, (0 : ℝ) < q w := fun w => by exact_mod_cast lt_of_lt_of_le two_pos (hS.primes.two w)
  have hne : ∀ σ : ℝ, 1 < σ → (σ : ℂ) - 1 ≠ 0 := fun σ h => sub_ne_zero.2 (by exact_mod_cast h.ne')
  have h1 : F 1 ≠ 0 := by
    intro h0
    have hc : ContinuousOn (fun t : ℝ => dslope F 1 t) (Set.Icc 1 2) := fun t ht => by
      refine (ContinuousAt.comp (g := dslope F 1) ?_ Complex.continuous_ofReal.continuousAt).continuousWithinAt
      rcases eq_or_ne (t : ℂ) 1 with e | e
      · rw [e]
        exact continuousAt_dslope_same.2 (by simpa using (hFa 1 one_pos).differentiableAt)
      · exact (continuousAt_dslope_of_ne e).2 (hFa t (by linarith [ht.1])).continuousAt
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine dirichlet_series_unbounded landauL newton_identities_low_degree euler_product_log_bound removable_singularity_holds (convergence_of_landau_euler landauL euler_product_log_bound)
      W q X d A hS Unit (fun _ => x) ⟨M, fun σ a b => ?_⟩
    have e1 : ∀ p, lterm q (A x) (A x) σ p = ((DirichletSeriesUnbounded₂.cc A (fun _ : Unit => x) p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)) : ℝ) : ℂ) :=
      fun p => by simpa using DirichletSeriesUnbounded₂.sum_lterm q A (fun _ : Unit => x) hq σ p
    have e2 := sub_smul_dslope F 1 (σ : ℂ)
    rw [h0, sub_zero, hFe σ a, smul_eq_mul] at e2
    have e3 := hM σ ⟨a.le, b⟩
    simp only [mul_left_cancel₀ (hne σ a) e2, Complex.norm_exp] at e3
    simp only [Finset.univ_unique, Finset.sum_singleton]
    simp only [e1, ← Complex.ofReal_tsum, Complex.ofReal_re] at e3 ⊢
    rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun p => mul_nonneg (DirichletSeriesUnbounded₂.cc_nonneg A _ p) (Real.exp_pos _).le)]
    exact le_trans (by linarith [Real.add_one_le_exp (∑' p, DirichletSeriesUnbounded₂.cc A (fun _ : Unit => x) p * Real.exp (-(DirichletSeriesUnbounded₂.ll q p * σ)))]) e3
  have h2 : ∀ t ∈ Set.Icc (1 : ℝ) 2, F t ≠ 0 := fun t ht => by
    rcases ht.1.eq_or_lt with e | e
    · rw [← e]; simpa using h1
    · rw [hFe t e]; exact mul_ne_zero (hne t e) (Complex.exp_ne_zero _)
  have hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2) := fun t ht =>
    (((hFa t (by linarith [ht.1])).continuousAt.comp Complex.continuous_ofReal.continuousAt).norm.log
      (norm_ne_zero_iff.2 (h2 t ht))).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ a b => ?_⟩
  have h3 := hM σ ⟨a.le, b⟩
  have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hFe σ a, norm_mul, hn, Complex.norm_exp, Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, Real.norm_eq_abs, add_comm] at h3
  exact h3
