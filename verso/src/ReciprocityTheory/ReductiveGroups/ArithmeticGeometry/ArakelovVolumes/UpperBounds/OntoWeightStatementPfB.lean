import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Establish `hphl` using `IW.phla_contOn X L`. Establish `hc : ContinuousOn (fun x => (∑ k, Complex.normSq (P k x)) * Real.exp (-phla X L x)) X.dom` using `(continuousOn_finsetSum _ fun k _ => Complex.continuous_normSq.comp_continuousOn (hP k)).mul (Real.continuous_exp.comp_continuousOn hphl.neg)`. Conclude with `hc.congr fun x hx => sum_pnorm_sq X L P hx`.
-/
theorem sumP_contOn {N : ℕ} (L : Wt X.Ψ r) (P : Fin N → Frame X.Ψ r → ℂ)
    (hP : ∀ k, ContinuousOn (P k) X.dom) :
    ContinuousOn (fun x => ∑ k, X.pnorm L (P k) x ^ 2) X.dom := by
  have hphl := IW.phla_contOn X L
  have hc : ContinuousOn (fun x => (∑ k, Complex.normSq (P k x)) * Real.exp (-phla X L x)) X.dom :=
    (continuousOn_finsetSum _ fun k _ => Complex.continuous_normSq.comp_continuousOn (hP k)).mul
      (Real.continuous_exp.comp_continuousOn hphl.neg)
  exact hc.congr fun x hx => sum_pnorm_sq X L P hx

/- English proof (translation)
Establish `hdo : IsOpen X.dom` using `IW.isOpen_dom X`. Establish `hwc : ∀ k, ContinuousOn (Xa.w k) X.dom` using `fun k => (Xa.w_van k).1.1.1.1.continuousOn`. Establish `hsc : ∀ k, ContinuousOn (Fl.s k) X.dom` using `fun k => (Fl.s_van k).1.1.1.1.continuousOn`. Establish `hSw` using `sumP_contOn Xa.L Xa.w hwc`. Establish `hSs` using `sumP_contOn Xa.L Fl.s hsc`.

Establish `hSw0 : ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≠ 0` using `fun x hx => by`. Rewrite using `[sum_pnorm_sq X _ _ hx]`. Conclude with `(mul_pos (sumw_pos Xa hx) (Real.exp_pos _)).ne'`. Establish `h1 : Measurable (X.dom.piecewise (fun x => ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x))) 0)` using `ContinuousOn.measurable_piecewise (ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn (IW.phla_contOn X _).neg)) continuousOn_const hdo.measurableSet`. Establish `h2 : Measurable (X.dom.piecewise (fun x => ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) 0)` using `ContinuousOn.measurable_piecewise ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).comp_continuousOn hSw) continuousOn_const hdo.measurableSet`.

Establish `h3 : Measurable (X.dom.piecewise (fun x => ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) 0)` using `ContinuousOn.measurable_piecewise ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).comp_continuousOn (hSs.div hSw hSw0)) continuousOn_const hdo.measurableSet`. Establish `key : WSk X Xa Fl = X.dom.piecewise (fun x => ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x))) 0 * X.dom.piecewise (fun x => ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) 0 * X.dom.piecewise (fun x => ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x …`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ X.dom`. Simplify using `only [WSk, if_pos hx, Pi.mul_apply, Set.piecewise_eq_of_mem _ _ _ hx]`.

Simplify using `only [WSk, if_neg hx, Pi.mul_apply, Set.piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply, zero_mul]`. Rewrite using `[key]`. Conclude with `(h1.mul h2).mul h3`.
-/
theorem WSk_meas (Xa : ArchInM X) (Fl : FlatM X Xa) : Measurable (WSk X Xa Fl) := by
  classical
  have hdo : IsOpen X.dom := IW.isOpen_dom X
  have hwc : ∀ k, ContinuousOn (Xa.w k) X.dom := fun k => (Xa.w_van k).1.1.1.1.continuousOn
  have hsc : ∀ k, ContinuousOn (Fl.s k) X.dom := fun k => (Fl.s_van k).1.1.1.1.continuousOn
  have hSw := sumP_contOn Xa.L Xa.w hwc
  have hSs := sumP_contOn Xa.L Fl.s hsc
  have hSw0 : ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≠ 0 := fun x hx => by
    rw [sum_pnorm_sq X _ _ hx]
    exact (mul_pos (sumw_pos Xa hx) (Real.exp_pos _)).ne'
  have h1 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x))) 0) :=
    ContinuousOn.measurable_piecewise
      (ENNReal.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn (IW.phla_contOn X _).neg))
      continuousOn_const hdo.measurableSet
  have h2 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) 0) :=
    ContinuousOn.measurable_piecewise
      ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).comp_continuousOn hSw)
      continuousOn_const hdo.measurableSet
  have h3 : Measurable (X.dom.piecewise
      (fun x => ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) /
        ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) 0) :=
    ContinuousOn.measurable_piecewise
      ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).comp_continuousOn
        (hSs.div hSw hSw0))
      continuousOn_const hdo.measurableSet
  have key : WSk X Xa Fl = X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x))) 0 *
      X.dom.piecewise
        (fun x => ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) 0 *
      X.dom.piecewise
        (fun x => ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) /
          ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) 0 := by
    funext x
    by_cases hx : x ∈ X.dom
    · simp only [WSk, if_pos hx, Pi.mul_apply, Set.piecewise_eq_of_mem _ _ _ hx]
    · simp only [WSk, if_neg hx, Pi.mul_apply, Set.piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply,
        zero_mul]
  rw [key]
  exact (h1.mul h2).mul h3

/- English proof (translation)
Rewrite using `[pnorm_eq X, pnorm_eq X, hP.2.2 γ hγ x hx, norm_mul, OntoE.chi_norm X L hγ, one_mul, normFactor_leftAction_holds r X L γ hγ x hx]`.
-/
theorem pnorm_lact (L : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec L P) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm L P (lact γ x) = X.pnorm L P x := by
  rw [pnorm_eq X, pnorm_eq X, hP.2.2 γ hγ x hx, norm_mul, OntoE.chi_norm X L hγ, one_mul,
    normFactor_leftAction_holds r X L γ hγ x hx]

/- English proof (translation)
Unfold `phla`. Rewrite using `[normFactor_leftAction_holds r X la γ hγ x hx]`.
-/
theorem phla_lact (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phla X la (lact γ x) = phla X la x := by
  unfold phla
  rw [normFactor_leftAction_holds r X la γ hγ x hx]

/- English proof (translation)
Establish `hwS : ∀ k, X.IsSec Xa.L (Xa.w k)` using `fun k => (Xa.w_van k).1.1.1`. Establish `hsS : ∀ k, X.IsSec Xa.L (Fl.s k)` using `fun k => (Fl.s_van k).1.1.1`. Use `⟨WSk_meas Xa Fl, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩` and prove the remaining obligations. Establish `hxb` using `OntoS.dom_rmul X hx hb`. Establish `hbc : 0 < ‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2`.

Use `OntoE.bchar_ne X (Xa.Fp + Xa.T • Xa.L) hb` as an intermediate fact. Check the signs of the components of the expression. Establish `hpw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x` using `fun k => IW.pnorm_rmul X normFactor_rightBorel_holds Xa.L (hwS k) hx hb`. Establish `hps : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x` using `fun k => IW.pnorm_rmul X normFactor_rightBorel_holds Xa.L (hsS k) hx hb`. Simplify using `only [WSk, if_pos hxb, if_pos hx, hpw, hps]`.

Rewrite using `[IW.exp_neg_phla_rmul X normFactor_rightBorel_holds _ hx hb, ENNReal.ofReal_div_of_pos hbc]`. Simplify using `only [div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxg` using `OntoS.dom_lact X hγ hx`. Establish `hpw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x` using `fun k => pnorm_lact Xa.L (hwS k) hγ hx`.

Establish `hps : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x` using `fun k => pnorm_lact Xa.L (hsS k) hγ hx`. Simplify using `only [WSk, if_pos hxg, if_pos hx, hpw, hps, phla_lact _ hγ hx]`.
-/
theorem WSk_metric (Xa : ArchInM X) (Fl : FlatM X Xa) :
    IsMetricW X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) := by
  have hwS : ∀ k, X.IsSec Xa.L (Xa.w k) := fun k => (Xa.w_van k).1.1.1
  have hsS : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  refine ⟨WSk_meas Xa Fl, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hxb := OntoS.dom_rmul X hx hb
    have hbc : 0 < ‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2 := by
      have := OntoE.bchar_ne X (Xa.Fp + Xa.T • Xa.L) hb
      positivity
    have hpw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x := fun k =>
      IW.pnorm_rmul X normFactor_rightBorel_holds Xa.L (hwS k) hx hb
    have hps : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x := fun k =>
      IW.pnorm_rmul X normFactor_rightBorel_holds Xa.L (hsS k) hx hb
    simp only [WSk, if_pos hxb, if_pos hx, hpw, hps]
    rw [IW.exp_neg_phla_rmul X normFactor_rightBorel_holds _ hx hb, ENNReal.ofReal_div_of_pos hbc]
    simp only [div_eq_mul_inv]
    ring
  · have hxg := OntoS.dom_lact X hγ hx
    have hpw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x := fun k =>
      pnorm_lact Xa.L (hwS k) hγ hx
    have hps : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x := fun k =>
      pnorm_lact Xa.L (hsS k) hγ hx
    simp only [WSk, if_pos hxg, if_pos hx, hpw, hps, phla_lact _ hγ hx]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Unfold `Data.nfac`. Conclude with `Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _`.
-/
theorem nfac_nonneg (la : Wt X.Ψ r) (x : Frame X.Ψ r) : 0 ≤ X.nfac la x := by
  unfold Data.nfac
  exact Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _

/- English proof (translation)
Rewrite using `[pnorm_eq X]`. Conclude with `mul_nonneg (norm_nonneg _) (nfac_nonneg la x)`.
-/
theorem pnorm_nonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x := by
  rw [pnorm_eq X]
  exact mul_nonneg (norm_nonneg _) (nfac_nonneg la x)

/- English proof (translation)
Establish `hT1 : (1 : ℝ) ≤ Xa.T`. Establish `h1` using `Xa.T_ge`. Establish `h2` using `Xa.n_ge`. Conclude with `(by nlinarith : 1 ≤ Xa.T)` after adjusting the coercions. Use `choose Cw hCw using fun k => (Xa.w_van k).1.1.2`.

Use `choose Cs hCs using fun k => (Fl.s_van k).1.1.2`. Use `set u : ℝ := (Xa.T : ℝ) - 1 / 2 with hu`. Establish `hu0 : 0 < u` using `by linarith`. Use `set Mw : ℝ := ∑ k, max (Cw k) 0 ^ 2 + 1 with hMw`. Use `set Ms : ℝ := ∑ k, max (Cs k) 0 ^ 2 + 1 with hMs`.

Establish `hMw0 : 0 < Mw` using `by positivity`. Establish `hMs0 : 0 < Ms` using `by positivity`. Use `⟨Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹, by positivity, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hSwM : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ Mw`. Establish `: ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ ∑ k, max (Cw k) 0 ^ 2` using `Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (pnorm_nonneg _ _ _) ((hCw k x hx).trans (le_max_left _ _)) 2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSsM : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 ≤ Ms`. Establish `: ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 ≤ ∑ k, max (Cs k) 0 ^ 2` using `Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (pnorm_nonneg _ _ _) ((hCs k x hx).trans (le_max_left _ _)) 2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSw : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2`.

Rewrite using `[sum_pnorm_sq X _ _ hx]`. Conclude with `mul_pos (sumw_pos Xa hx) (Real.exp_pos _)`. Establish `hSs0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2` using `Finset.sum_nonneg fun k _ => sq_nonneg _`. Use `set Sw := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hSwd`. Use `set Ss := ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 with hSsd`.

Use `set e := Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x) with he`. Establish `he0 : 0 < e` using `Real.exp_pos _`. Simplify using `only [WSk, if_pos hx]`. Rewrite using `[← hSwd, ← hSsd, ← he]`. Break down `hSs0.eq_or_lt with hS | hS` into its components or cases.

Rewrite using `[← hS, zero_div, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith), ENNReal.mul_top]`. Conclude with `le_top`. Conclude with `mul_ne_zero (ENNReal.ofReal_pos.mpr he0).ne' (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hSw) ENNReal.ofReal_ne_top).ne'`. Rewrite using `[ENNReal.ofReal_rpow_of_pos hSw, ENNReal.ofReal_rpow_of_pos (div_pos hS hSw), ← ENNReal.ofReal_mul he0.le, ← ENNReal.ofReal_mul (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `eq : Sw ^ (-(Xa.T : ℝ)) * (Ss / Sw) ^ (-u) = Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹`. Establish `hsplit : Sw ^ u = Sw ^ (Xa.T : ℝ) * Sw ^ (-(1 / 2 : ℝ))`. Rewrite using `[← Real.rpow_add hSw]`. Use `congr 1`. Rewrite using `[Real.rpow_neg hSw.le, Real.rpow_neg (div_pos hS hSw).le, Real.div_rpow hS.le hSw.le, inv_div, hsplit]`.

Establish `h1 : 0 < Sw ^ (Xa.T : ℝ)` using `Real.rpow_pos_of_pos hSw _`. Establish `h2 : 0 < Ss ^ u` using `Real.rpow_pos_of_pos hS _`. Clear the denominators using the available nonvanishing facts. Establish `hA : Mw ^ (-(1 / 2 : ℝ)) ≤ Sw ^ (-(1 / 2 : ℝ))` using `Real.rpow_le_rpow_of_nonpos hSw hSwM (by norm_num)`. Establish `hB : (Ms ^ u)⁻¹ ≤ (Ss ^ u)⁻¹` using `inv_anti₀ (Real.rpow_pos_of_pos hS _) (Real.rpow_le_rpow hS.le hSsM hu0.le)`.

Establish `hC : Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹ ≤ Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹` using `mul_le_mul hA hB (by positivity) (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem WSk_lower (Xa : ArchInM X) (Fl : FlatM X Xa) :
    WLower X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) := by
  have hT1 : (1 : ℝ) ≤ Xa.T := by
    have h1 := Xa.T_ge
    have h2 := Xa.n_ge
    exact_mod_cast (by nlinarith : 1 ≤ Xa.T)
  choose Cw hCw using fun k => (Xa.w_van k).1.1.2
  choose Cs hCs using fun k => (Fl.s_van k).1.1.2
  set u : ℝ := (Xa.T : ℝ) - 1 / 2 with hu
  have hu0 : 0 < u := by linarith
  set Mw : ℝ := ∑ k, max (Cw k) 0 ^ 2 + 1 with hMw
  set Ms : ℝ := ∑ k, max (Cs k) 0 ^ 2 + 1 with hMs
  have hMw0 : 0 < Mw := by positivity
  have hMs0 : 0 < Ms := by positivity
  refine ⟨Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹, by positivity, fun x hx => ?_⟩
  have hSwM : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ Mw := by
    have : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ ∑ k, max (Cw k) 0 ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (pnorm_nonneg _ _ _)
        ((hCw k x hx).trans (le_max_left _ _)) 2
    linarith
  have hSsM : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 ≤ Ms := by
    have : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 ≤ ∑ k, max (Cs k) 0 ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (pnorm_nonneg _ _ _)
        ((hCs k x hx).trans (le_max_left _ _)) 2
    linarith
  have hSw : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    rw [sum_pnorm_sq X _ _ hx]
    exact mul_pos (sumw_pos Xa hx) (Real.exp_pos _)
  have hSs0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  set Sw := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hSwd
  set Ss := ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 with hSsd
  set e := Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x) with he
  have he0 : 0 < e := Real.exp_pos _
  simp only [WSk, if_pos hx]
  rw [← hSwd, ← hSsd, ← he]
  rcases hSs0.eq_or_lt with hS | hS
  · rw [← hS, zero_div, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top]
    · exact le_top
    · exact mul_ne_zero (ENNReal.ofReal_pos.mpr he0).ne'
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hSw) ENNReal.ofReal_ne_top).ne'
  · rw [ENNReal.ofReal_rpow_of_pos hSw, ENNReal.ofReal_rpow_of_pos (div_pos hS hSw),
      ← ENNReal.ofReal_mul he0.le, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have eq : Sw ^ (-(Xa.T : ℝ)) * (Ss / Sw) ^ (-u) = Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ := by
      have hsplit : Sw ^ u = Sw ^ (Xa.T : ℝ) * Sw ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hSw]
        congr 1
      rw [Real.rpow_neg hSw.le, Real.rpow_neg (div_pos hS hSw).le, Real.div_rpow hS.le hSw.le,
        inv_div, hsplit]
      have h1 : 0 < Sw ^ (Xa.T : ℝ) := Real.rpow_pos_of_pos hSw _
      have h2 : 0 < Ss ^ u := Real.rpow_pos_of_pos hS _
      field_simp
    have hA : Mw ^ (-(1 / 2 : ℝ)) ≤ Sw ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hSw hSwM (by norm_num)
    have hB : (Ms ^ u)⁻¹ ≤ (Ss ^ u)⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hS _) (Real.rpow_le_rpow hS.le hSsM hu0.le)
    have hC : Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹ ≤ Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ :=
      mul_le_mul hA hB (by positivity) (by positivity)
    calc Mw ^ (-(1 / 2 : ℝ)) * (Ms ^ u)⁻¹ * e ≤ Sw ^ (-(1 / 2 : ℝ)) * (Ss ^ u)⁻¹ * e :=
          mul_le_mul_of_nonneg_right hC he0.le
      _ = e * Sw ^ (-(Xa.T : ℝ)) * (Ss / Sw) ^ (-u) := by rw [mul_assoc e, eq]; ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
