import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntUv

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Bump

def bump0 : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

def chi (w : ℂ) : ℂ := ((bump0 w : ℝ) : ℂ)

def chin (n : ℕ) (w : ℂ) : ℂ := chi (((n : ℝ) + 1)⁻¹ • w)

/- English proof (translation)
Unfold `chi`. Conclude with `Complex.ofRealCLM.contDiff.comp bump0.contDiff`.
-/
theorem chi_contDiff : ContDiff ℝ ∞ chi := by
  unfold chi
  exact Complex.ofRealCLM.contDiff.comp bump0.contDiff

/- English proof (translation)
Unfold `chin`. Conclude with `chi_contDiff.comp (contDiff_const_smul _)`.
-/
theorem chin_contDiff (n : ℕ) : ContDiff ℝ ∞ (chin n) := by
  unfold chin
  exact chi_contDiff.comp (contDiff_const_smul _)

/- English proof (translation)
Unfold `chin chi`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg bump0.nonneg]`. Conclude with `bump0.le_one`.
-/
theorem norm_chin_le (n : ℕ) (w : ℂ) : ‖chin n w‖ ≤ 1 := by
  unfold chin chi
  rw [Complex.norm_real, Real.norm_of_nonneg bump0.nonneg]
  exact bump0.le_one

/- English proof (translation)
Unfold `chin chi`. Rewrite using `[bump0.zero_of_le_dist, Complex.ofReal_zero]`. Use `show (2 : ℝ) ≤ dist (((n : ℝ) + 1)⁻¹ • w) 0`. Rewrite using `[dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹), inv_mul_eq_div, le_div_iff₀ (by positivity)]`. Conclude with `hw`.
-/
theorem chin_zero (n : ℕ) (w : ℂ) (hw : 2 * ((n : ℝ) + 1) ≤ ‖w‖) : chin n w = 0 := by
  unfold chin chi
  rw [bump0.zero_of_le_dist, Complex.ofReal_zero]
  show (2 : ℝ) ≤ dist (((n : ℝ) + 1)⁻¹ • w) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹),
    inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact hw

/- English proof (translation)
Establish `hopen : IsOpen {v : ℂ | ‖v‖ < (n : ℝ) + 1}` using `isOpen_lt continuous_norm continuous_const`. Use `filter_upwards [hopen.mem_nhds hw] with v hv`. Use `show chin n v = 1`. Unfold `chin chi`. Rewrite using `[bump0.one_of_mem_closedBall, Complex.ofReal_one]`.

Rewrite using `[Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)]`. Use `show ((n : ℝ) + 1)⁻¹ * ‖v‖ ≤ 1`. Rewrite using `[inv_mul_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chin_eventually_one (n : ℕ) (w : ℂ) (hw : ‖w‖ < (n : ℝ) + 1) : chin n =ᶠ[𝓝 w] fun _ => 1 := by
  have hopen : IsOpen {v : ℂ | ‖v‖ < (n : ℝ) + 1} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hw] with v hv
  show chin n v = 1
  unfold chin chi
  rw [bump0.one_of_mem_closedBall, Complex.ofReal_one]
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)]
  show ((n : ℝ) + 1)⁻¹ * ‖v‖ ≤ 1
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

/- English proof (translation)
Rewrite using `[(chin_eventually_one n w hw).fderiv_eq]`. Conclude with `fderiv_const_apply _`.
-/
theorem fderiv_chin_zero (n : ℕ) (w : ℂ) (hw : ‖w‖ < (n : ℝ) + 1) : fderiv ℝ (chin n) w = 0 := by
  rw [(chin_eventually_one n w hw).fderiv_eq]
  exact fderiv_const_apply _

/- English proof (translation)
Establish `hcs : HasCompactSupport chi` using `by show HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ bump0)`. Conclude with `bump0.hasCompactSupport.comp_left Complex.ofReal_zero`. Conclude with `(chi_contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support (hcs.fderiv ℝ)`.
-/
theorem exists_fderiv_chi_bound : ∃ C : ℝ, ∀ w, ‖fderiv ℝ chi w‖ ≤ C := by
  have hcs : HasCompactSupport chi := by
    show HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ bump0)
    exact bump0.hasCompactSupport.comp_left Complex.ofReal_zero
  exact (chi_contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support (hcs.fderiv ℝ)

/- English proof (translation)
Establish `hs0 : (0 : ℝ) < ((n : ℝ) + 1)⁻¹` using `by positivity`. Establish `hs1 : ((n : ℝ) + 1)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])`. Establish `hd : HasFDerivAt (chin n) ((fderiv ℝ chi (((n : ℝ) + 1)⁻¹ • w)).comp (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ)) w`. Establish `h1` using `(chi_contDiff.differentiable (by simp) (((n : ℝ) + 1)⁻¹ • w)).hasFDerivAt`. Establish `h2 : HasFDerivAt (fun v : ℂ => ((n : ℝ) + 1)⁻¹ • v) (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ) w` using `(((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt`.

Conclude with `h1.comp w h2`. Establish `hn : ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ ≤ 1`. Rewrite using `[norm_smul, Real.norm_of_nonneg hs0.le]`. Use `(ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1)` as an intermediate fact. Use polynomial arithmetic with `[norm_nonneg (ContinuousLinearMap.id ℝ ℂ)]`.

Rewrite using `[hd.fderiv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_fderiv_chin_le {C : ℝ} (hC : ∀ w, ‖fderiv ℝ chi w‖ ≤ C) (n : ℕ) (w : ℂ) :
    ‖fderiv ℝ (chin n) w‖ ≤ C := by
  have hs0 : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have hs1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hd : HasFDerivAt (chin n)
      ((fderiv ℝ chi (((n : ℝ) + 1)⁻¹ • w)).comp (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ)) w := by
    have h1 := (chi_contDiff.differentiable (by simp) (((n : ℝ) + 1)⁻¹ • w)).hasFDerivAt
    have h2 : HasFDerivAt (fun v : ℂ => ((n : ℝ) + 1)⁻¹ • v) (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ) w :=
      (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt
    exact h1.comp w h2
  have hn : ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
    have := (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1)
    nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ ℂ)]
  rw [hd.fderiv]
  calc _ ≤ ‖fderiv ℝ chi (((n : ℝ) + 1)⁻¹ • w)‖ * ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * 1 := mul_le_mul (hC _) hn (norm_nonneg _) (le_trans (norm_nonneg _) (hC 0))
    _ = C := mul_one C

/- English proof (translation)
Use `show ‖(1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I)‖ ≤ _`. Use `set L := fderiv ℝ f w`. Establish `h1 : ‖L 1‖ ≤ ‖L‖` using `by simpa using L.le_opNorm 1`. Establish `h2 : ‖L Complex.I‖ ≤ ‖L‖` using `by simpa using L.le_opNorm Complex.I`. Establish `h3 : ‖L 1 - Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖L Complex.I‖`.

Combine the equalities or inequalities in the displayed calculation. Establish `hh : ‖(1 / 2 : ℂ)‖ = 1 / 2` using `by norm_num`. Rewrite using `[norm_mul, hh]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_dZ_le (f : ℂ → ℂ) (w : ℂ) : ‖NF.dZ f w‖ ≤ ‖fderiv ℝ f w‖ := by
  show ‖(1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I)‖ ≤ _
  set L := fderiv ℝ f w
  have h1 : ‖L 1‖ ≤ ‖L‖ := by simpa using L.le_opNorm 1
  have h2 : ‖L Complex.I‖ ≤ ‖L‖ := by simpa using L.le_opNorm Complex.I
  have h3 : ‖L 1 - Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖L Complex.I‖ := by
    calc ‖L 1 - Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖Complex.I * L Complex.I‖ := norm_sub_le _ _
      _ = ‖L 1‖ + ‖L Complex.I‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [norm_mul, hh]
  linarith

/- English proof (translation)
Use `show ‖(1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I)‖ ≤ _`. Use `set L := fderiv ℝ f w`. Establish `h1 : ‖L 1‖ ≤ ‖L‖` using `by simpa using L.le_opNorm 1`. Establish `h2 : ‖L Complex.I‖ ≤ ‖L‖` using `by simpa using L.le_opNorm Complex.I`. Establish `h3 : ‖L 1 + Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖L Complex.I‖`.

Combine the equalities or inequalities in the displayed calculation. Establish `hh : ‖(1 / 2 : ℂ)‖ = 1 / 2` using `by norm_num`. Rewrite using `[norm_mul, hh]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_dZb_le (f : ℂ → ℂ) (w : ℂ) : ‖NF.dZb f w‖ ≤ ‖fderiv ℝ f w‖ := by
  show ‖(1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I)‖ ≤ _
  set L := fderiv ℝ f w
  have h1 : ‖L 1‖ ≤ ‖L‖ := by simpa using L.le_opNorm 1
  have h2 : ‖L Complex.I‖ ≤ ‖L‖ := by simpa using L.le_opNorm Complex.I
  have h3 : ‖L 1 + Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖L Complex.I‖ := by
    calc ‖L 1 + Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖Complex.I * L Complex.I‖ := norm_add_le _ _
      _ = ‖L 1‖ + ‖L Complex.I‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [norm_mul, hh]
  linarith

/- English proof (translation)
Establish `hd : ContDiff ℝ ∞ (fderiv ℝ f)` using `(contDiff_infty_iff_fderiv.1 hf).2`. Establish `h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1)` using `hd.clm_apply contDiff_const`. Establish `hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I)` using `hd.clm_apply contDiff_const`. Use `show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I))`. Conclude with `contDiff_const.mul (h1.sub (contDiff_const.mul hI))`.
-/
theorem dZ_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZ f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.sub (contDiff_const.mul hI))

/- English proof (translation)
Establish `hd : ContDiff ℝ ∞ (fderiv ℝ f)` using `(contDiff_infty_iff_fderiv.1 hf).2`. Establish `h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1)` using `hd.clm_apply contDiff_const`. Establish `hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I)` using `hd.clm_apply contDiff_const`. Use `show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I))`. Conclude with `contDiff_const.mul (h1.add (contDiff_const.mul hI))`.
-/
theorem dZb_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZb f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

/- English proof (translation)
Use `show (1 / 2 : ℂ) * (fderiv ℝ (chin n) w 1 - Complex.I * fderiv ℝ (chin n) w Complex.I) = 0`. Rewrite using `[fderiv_chin_zero n w hw]`. Simplify using the standard rewrite rules.
-/
theorem dZ_chin_zero (n : ℕ) (w : ℂ) (hw : ‖w‖ < (n : ℝ) + 1) : NF.dZ (chin n) w = 0 := by
  show (1 / 2 : ℂ) * (fderiv ℝ (chin n) w 1 - Complex.I * fderiv ℝ (chin n) w Complex.I) = 0
  rw [fderiv_chin_zero n w hw]
  simp

/- English proof (translation)
Use `show (1 / 2 : ℂ) * (fderiv ℝ (chin n) w 1 + Complex.I * fderiv ℝ (chin n) w Complex.I) = 0`. Rewrite using `[fderiv_chin_zero n w hw]`. Simplify using the standard rewrite rules.
-/
theorem dZb_chin_zero (n : ℕ) (w : ℂ) (hw : ‖w‖ < (n : ℝ) + 1) : NF.dZb (chin n) w = 0 := by
  show (1 / 2 : ℂ) * (fderiv ℝ (chin n) w 1 + Complex.I * fderiv ℝ (chin n) w Complex.I) = 0
  rw [fderiv_chin_zero n w hw]
  simp

/- English proof (translation)
Use `filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖w‖] with n hn`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eventually_lt (w : ℂ) : ∀ᶠ n : ℕ in atTop, ‖w‖ < (n : ℝ) + 1 := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖w‖] with n hn
  linarith

end Bump

end Formalism.FourierDecayAlt.P5.HerB
