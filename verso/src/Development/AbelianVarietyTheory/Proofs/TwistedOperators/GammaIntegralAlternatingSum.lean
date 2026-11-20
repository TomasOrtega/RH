import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExponentialGammaIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GammaFunctionBoundedSupportStatement

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.Chamber

/- English proof (translation)
Simplify using `[eLC, Complex.norm_exp]`.
-/
theorem norm_eLC {k : ℕ} (l m H : A0 k) : ‖eLC l m H‖ = Real.exp (-⟪m, H⟫_ℝ) := by
  simp [eLC, Complex.norm_exp]

/- English proof (translation)
Establish `h : Continuous fun t : ℝ => eLC l (t • m) H` using `by unfold eLC; fun_prop`. Simplify `h.tendsto 0` using `[eLC_zero]`.
-/
theorem tendsto_eLC_smul {k : ℕ} (l m H : A0 k) :
    Tendsto (fun t : ℝ => eLC l (t • m) H) (𝓝 0) (𝓝 (eL l H)) := by
  have h : Continuous fun t : ℝ => eLC l (t • m) H := by unfold eLC; fun_prop
  simpa [eLC_zero] using h.tendsto 0

/- English proof (translation)
Establish `hc : ContinuousAt (fun t : ℝ => epsOfC s b l (t • m)) 0`. Unfold `epsOfC`. Use `continuousAt_const.mul (tendsto_finsetProd _ fun u hu => ?_)` and prove the remaining obligations. Use `ContinuousAt.inv₀ (f := fun t : ℝ => Complex.I * (⟪l, b u⟫_ℝ : ℝ) - (⟪t • m, b u⟫_ℝ : ℝ)) (by fun_prop) ?_` and prove the remaining obligations. Simplify using `using h u hu`.

Simplify `hc.tendsto` using `[epsOfC_zero]`.
-/
theorem tendsto_epsOfC_smul {k : ℕ} (s : Finset (SV k)) (b : SV k → A0 k) (l m : A0 k)
    (h : ∀ u ∈ s, ⟪l, b u⟫_ℝ ≠ 0) :
    Tendsto (fun t : ℝ => epsOfC s b l (t • m)) (𝓝 0) (𝓝 (epsOf s b l)) := by
  have hc : ContinuousAt (fun t : ℝ => epsOfC s b l (t • m)) 0 := by
    unfold epsOfC
    refine continuousAt_const.mul (tendsto_finsetProd _ fun u hu => ?_)
    refine ContinuousAt.inv₀ (f := fun t : ℝ => Complex.I * (⟪l, b u⟫_ℝ : ℝ) - (⟪t • m, b u⟫_ℝ : ℝ)) (by fun_prop) ?_
    simpa using h u hu
  simpa [epsOfC_zero] using hc.tendsto

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.T.gamma_function_bounded_support k P R Y hP hR`. Take `⟨m, hm⟩` from `GlobalTheory.T.exponential_gamma_integral_formula k P R Y hP hR`. Establish `hb : ∀ (t : ℝ) (H : aMQ (aP P) R), |t| ≤ 1 → gamP P R Y H ≠ 0 → Real.exp (-⟪t • m, (H : A0 k)⟫_ℝ) ≤ Real.exp (‖m‖ * C)` using `fun t H ht h => by`. Use `Real.exp_le_exp.2 ((neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans ?_))` and prove the remaining obligations. Use `mul_le_mul ?_ (hC H H.2 h) (norm_nonneg _) (norm_nonneg _)` and prove the remaining obligations.

Rewrite using `[norm_smul, Real.norm_eq_abs]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) ht`. Establish `hint : Integrable (fun H : aMQ (aP P) R => (gamP P R Y H : ℂ))`. Establish `h1` using `(hm 1 one_pos 0).1`. Establish `e : (fun H : aMQ (aP P) R => (gamP P R Y H : ℂ)) = fun H : aMQ (aP P) R => eLC 0 ((-1 : ℝ) • m) H * (eLC 0 ((1 : ℝ) • m) H * gamP P R Y H)`.

Use function extensionality and compare the values at `H`. Rewrite using `[← mul_assoc, eLC, eLC, ← Complex.exp_add]`. Simplify using the standard rewrite rules. Establish `hc : Continuous fun H : aMQ (aP P) R => eLC 0 ((-1 : ℝ) • m) H` using `by unfold eLC; fun_prop`. Rewrite using `[e]`.

Use `(h1.norm.const_mul (Real.exp (‖m‖ * C))).mono' (hc.aestronglyMeasurable.mul h1.1) (Eventually.of_forall fun H => ?_)` and prove the remaining obligations. Distinguish the cases in `h : gamP P R Y H = 0`. Simplify using `[h]`. Rewrite using `[norm_mul, norm_eLC]`. Conclude with `mul_le_mul_of_nonneg_right (hb _ H (by simp) h) (norm_nonneg _)`.

Use `⟨by simpa using hint.re, fun l hl => ?_⟩` and prove the remaining obligations. Establish `hL : Tendsto (fun t : ℝ => ∫ H : aMQ (aP P) R, eLC l (t • m) H * gamP P R Y H) (𝓝[>] 0) (𝓝 (∫ H : aMQ (aP P) R, eL l H * gamP P R Y H))`. Use `tendsto_integral_filter_of_dominated_convergence (fun H => Real.exp (‖m‖ * C) * ‖(gamP P R Y H : ℂ)‖) ?_ ?_ (hint.norm.const_mul _) (Eventually.of_forall fun H => ((tendsto_eLC_smul l m H).mono_left nhdsWithin_le_nhds).mul_const _)` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with t ht using (hm t ht l).1.1`. Use `filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht`.

Use `Eventually.of_forall fun H => ?_` and prove the remaining obligations. Distinguish the cases in `h : gamP P R Y H = 0`. Simplify using `[h]`. Rewrite using `[norm_mul, norm_eLC]`. Conclude with `mul_le_mul_of_nonneg_right (hb _ H (by rw [abs_of_pos ht.1]; exact ht.2.le) h) (norm_nonneg _)`.

Establish `hRt : Tendsto (fun t : ℝ => ∑ S ∈ between P R, (-1) ^ (P \ S).card * epsOfC (P \ S) (wt S) l (t • m) * epsOfC (S \ R) (rt S) l (t • m) * eLC l (t • m) (pr S Y - pr R Y)) (𝓝 0) (𝓝 (∑ S ∈ between P R, (-1) ^ (P \ S).card * epsHat P S l * eps S R l * eL l (pr S Y - pr R Y)))`. Use `tendsto_finsetSum _ fun S hS => ?_` and prove the remaining obligations. Establish `hSP : S ⊆ P` using `mem_powerset.1 (mem_filter.1 hS).1`. Use `(((tendsto_epsOfC_smul _ _ l m (hl P hP S hSP)).const_mul _).mul (tendsto_epsOfC_smul _ _ l m fun u hu => ?_)).mul (tendsto_eLC_smul l m _)` and prove the remaining obligations. Conclude with `hl S (hP.mono hSP) (S.erase u) (erase_subset _ _) u (mem_sdiff.2 ⟨(mem_sdiff.1 hu).1, notMem_erase _ _⟩)`.

Use `tendsto_nhds_unique hL ((hRt.mono_left nhdsWithin_le_nhds).congr' ?_)` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with t ht using (hm t ht l).2.symm`.
-/
theorem integrable_gamma_and_integral_exp_mul (k : ℕ) (P R : Finset (SV k)) (Y : A0 k) (hP : IsPar P) (hR : R ⊆ P) :
    Integrable (fun H : aMQ (aP P) R => gamP P R Y H) ∧ ∀ l ∈ generic k,
      ∫ H : aMQ (aP P) R, eL l H * gamP P R Y H =
        ∑ S ∈ between P R, (-1) ^ (P \ S).card * epsHat P S l * eps S R l * eL l (pr S Y - pr R Y) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.gamma_function_bounded_support k P R Y hP hR
  obtain ⟨m, hm⟩ := GlobalTheory.T.exponential_gamma_integral_formula k P R Y hP hR
  have hb : ∀ (t : ℝ) (H : aMQ (aP P) R), |t| ≤ 1 → gamP P R Y H ≠ 0 →
      Real.exp (-⟪t • m, (H : A0 k)⟫_ℝ) ≤ Real.exp (‖m‖ * C) := fun t H ht h => by
    refine Real.exp_le_exp.2 ((neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans ?_))
    refine mul_le_mul ?_ (hC H H.2 h) (norm_nonneg _) (norm_nonneg _)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hint : Integrable (fun H : aMQ (aP P) R => (gamP P R Y H : ℂ)) := by
    have h1 := (hm 1 one_pos 0).1
    have e : (fun H : aMQ (aP P) R => (gamP P R Y H : ℂ)) =
        fun H : aMQ (aP P) R => eLC 0 ((-1 : ℝ) • m) H * (eLC 0 ((1 : ℝ) • m) H * gamP P R Y H) := by
      funext H
      rw [← mul_assoc, eLC, eLC, ← Complex.exp_add]
      simp
    have hc : Continuous fun H : aMQ (aP P) R => eLC 0 ((-1 : ℝ) • m) H := by unfold eLC; fun_prop
    rw [e]
    refine (h1.norm.const_mul (Real.exp (‖m‖ * C))).mono' (hc.aestronglyMeasurable.mul h1.1)
      (Eventually.of_forall fun H => ?_)
    by_cases h : gamP P R Y H = 0
    · simp [h]
    · rw [norm_mul, norm_eLC]
      exact mul_le_mul_of_nonneg_right (hb _ H (by simp) h) (norm_nonneg _)
  refine ⟨by simpa using hint.re, fun l hl => ?_⟩
  have hL : Tendsto (fun t : ℝ => ∫ H : aMQ (aP P) R, eLC l (t • m) H * gamP P R Y H) (𝓝[>] 0)
      (𝓝 (∫ H : aMQ (aP P) R, eL l H * gamP P R Y H)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun H => Real.exp (‖m‖ * C) * ‖(gamP P R Y H : ℂ)‖) ?_ ?_ (hint.norm.const_mul _)
      (Eventually.of_forall fun H => ((tendsto_eLC_smul l m H).mono_left nhdsWithin_le_nhds).mul_const _)
    · filter_upwards [self_mem_nhdsWithin] with t ht using (hm t ht l).1.1
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
      refine Eventually.of_forall fun H => ?_
      by_cases h : gamP P R Y H = 0
      · simp [h]
      · rw [norm_mul, norm_eLC]
        exact mul_le_mul_of_nonneg_right (hb _ H (by rw [abs_of_pos ht.1]; exact ht.2.le) h) (norm_nonneg _)
  have hRt : Tendsto (fun t : ℝ => ∑ S ∈ between P R, (-1) ^ (P \ S).card * epsOfC (P \ S) (wt S) l (t • m) *
      epsOfC (S \ R) (rt S) l (t • m) * eLC l (t • m) (pr S Y - pr R Y)) (𝓝 0)
      (𝓝 (∑ S ∈ between P R, (-1) ^ (P \ S).card * epsHat P S l * eps S R l * eL l (pr S Y - pr R Y))) := by
    refine tendsto_finsetSum _ fun S hS => ?_
    have hSP : S ⊆ P := mem_powerset.1 (mem_filter.1 hS).1
    refine (((tendsto_epsOfC_smul _ _ l m (hl P hP S hSP)).const_mul _).mul
      (tendsto_epsOfC_smul _ _ l m fun u hu => ?_)).mul (tendsto_eLC_smul l m _)
    exact hl S (hP.mono hSP) (S.erase u) (erase_subset _ _) u
      (mem_sdiff.2 ⟨(mem_sdiff.1 hu).1, notMem_erase _ _⟩)
  refine tendsto_nhds_unique hL ((hRt.mono_left nhdsWithin_le_nhds).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht using (hm t ht l).2.symm

end GlobalTheory.Chamber

end
