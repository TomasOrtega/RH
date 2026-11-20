import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.NeZeroOne
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym

noncomputable section

namespace UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS UpperTheory.ConvolutionTheory.Rs

/- English proof (translation)
Introduce `W q X d A hS x y`. Take `⟨F, σ₀, hF, he⟩` from `hS.rs x y`. Use `⟨F, by simpa using hF 1 one_pos, fun σ hσ => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [eq_exp hS x y F (fun s => (s - 1) ^ (if x = y then 1 else 0)) σ₀ hF (fun t => (analyticAt_id.sub analyticAt_const).pow _) (fun t ht => by rw [he t ht]; split_ifs <;> simp) σ hσ]`.
-/
theorem expRight : ExpRight := by
  intro W q X d A hS x y
  obtain ⟨F, σ₀, hF, he⟩ := hS.rs x y
  refine ⟨F, by simpa using hF 1 one_pos, fun σ hσ => ?_⟩
  classical
  rw [eq_exp hS x y F (fun s => (s - 1) ^ (if x = y then 1 else 0)) σ₀ hF
    (fun t => (analyticAt_id.sub analyticAt_const).pow _) (fun t ht => by rw [he t ht]; split_ifs <;> simp) σ hσ]

/- English proof (translation)
Introduce `W q X d A hS x y`. Take `⟨F, σ₀, hF, he⟩` from `hS.rs x y`. Establish `hn` using `exp_re hS x y F σ₀ hF he`. Establish `h0 : ∀ t ∈ Set.Icc (1 : ℝ) 2, ‖F t‖ ≠ 0` using `fun t ht => by`. Break down `ht.1.eq_or_lt with h | h` into its components or cases.

Substitute `h` using the available equality. Simplify using `using ne_zero_one hS x y F σ₀ hF he`. Rewrite using `[hn t h]`. Use `mul_ne_zero ?_ (Real.exp_pos _).ne'` and prove the remaining obligations. Use `split_ifs`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `one_ne_zero`. Establish `hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2)` using `ContinuousOn.log (fun t ht => ((hF t (by linarith [ht.1])).continuousAt.comp (f := fun t : ℝ => (t : ℂ)) Complex.continuous_ofReal.continuousAt).norm.continuousWithinAt) h0`. Take `⟨M, hM⟩` from `isCompact_Icc.exists_bound_of_continuousOn hc`. Use `⟨M, fun σ h1 h2 => ?_⟩` and prove the remaining obligations.

Establish `h` using `hM σ ⟨h1.le, h2⟩`. Rewrite `h` using `[hn σ h1, Real.norm_eq_abs]`. Unfold `dre`. Use `split_ifs at h ⊢`. Rewrite `h` using `[Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]`.

Rewrite using `[sub_neg_eq_add, add_comm]` and apply the resulting hypothesis. Rewrite `h` using `[one_mul, Real.log_exp, ← sub_zero (Complex.re _)]`. Then use the resulting hypothesis.
-/
theorem logAsym : LogAsym := by
  intro W q X d A hS x y
  obtain ⟨F, σ₀, hF, he⟩ := hS.rs x y
  have hn := exp_re hS x y F σ₀ hF he
  have h0 : ∀ t ∈ Set.Icc (1 : ℝ) 2, ‖F t‖ ≠ 0 := fun t ht => by
    rcases ht.1.eq_or_lt with h | h
    · subst h
      simpa using ne_zero_one hS x y F σ₀ hF he
    · rw [hn t h]
      refine mul_ne_zero ?_ (Real.exp_pos _).ne'
      split_ifs
      · linarith
      · exact one_ne_zero
  have hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2) := ContinuousOn.log (fun t ht =>
    ((hF t (by linarith [ht.1])).continuousAt.comp (f := fun t : ℝ => (t : ℂ))
      Complex.continuous_ofReal.continuousAt).norm.continuousWithinAt) h0
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ h1 h2 => ?_⟩
  have h := hM σ ⟨h1.le, h2⟩
  rw [hn σ h1, Real.norm_eq_abs] at h
  unfold dre
  split_ifs at h ⊢
  · rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp] at h
    rwa [sub_neg_eq_add, add_comm]
  · rwa [one_mul, Real.log_exp, ← sub_zero (Complex.re _)] at h

end UpperTheory.ConvolutionTheory.R
