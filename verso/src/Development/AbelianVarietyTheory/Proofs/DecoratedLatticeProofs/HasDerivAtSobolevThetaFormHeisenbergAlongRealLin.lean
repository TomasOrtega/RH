import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

noncomputable section

namespace GlobalTheory.MatCoeffDeriv

open GlobalTheory.FockCompare

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T ℓ hℓ f hf M hM hMf w`. Establish `hL : IsRealDir T S M` using `⟨hM, hMf⟩`. Establish `hg : IsThetaFunO ψ S T (heisO ψ S T w f)` using `GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w`. Use `set g := heisO ψ S T w f with hg_def`. Use `set c : ℝ → ℂ := fun s => ψ (symplOH S T w (M s)) with hc_def`.

Establish `lsub : ∀ a b, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b → ℓ (a - b) = ℓ a - ℓ b`. Introduce `a b ha hb`. Use `hℓ.add (a - b) b (GlobalTheory.OrientedHeis.theta_sub ha hb) hb` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Establish `hce : c = fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1)))))`. Use function extensionality and compare the values at `s`. Use `show ψ (symplOH S T w (M s)) = _`.

Rewrite using `[(smooth_iff_sm_and_real_lines D θ σ h T S).2.1 M hL s, GlobalTheory.OrientedHeis.psi_symplOH h hψ, map_smul]`. Both sides reduce to the same expression. Establish `hcd : HasDerivAt c (deriv c 0) 0`. Use `DifferentiableAt.hasDerivAt ?_` and prove the remaining obligations. Establish `h2 : ContDiff ℝ ∞ fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1)))))` using `Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)))`.

Rewrite using `[hce]`. Conclude with `h2.differentiable (by simp) 0`. Establish `hc0 : c 0 = 1` using `by show ψ (symplOH S T w (M 0)) = 1`. Rewrite using `[M.map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, ψ.map_zero_eq_one]`. Establish `hcne : ∀ s, c s ≠ 0`.

Introduce `s`. Rewrite using `[hce]`. Conclude with `Complex.exp_ne_zero _`. Establish `hF : ∀ s, heisO ψ S T (w + M s) f = c s • heisO ψ S T (M s) g`. Introduce `s`.

Rewrite using `[hg_def, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, GlobalTheory.FinTranslate.symplOH_skew (S := S) (T := T) w (M s), add_neg_cancel, ψ.map_zero_eq_one, one_smul, add_comm]`. Take `⟨U, hUo, hUl⟩` from `hg.level`. Take `⟨d, C, hC⟩` from `hℓ.bound U hUo`. Establish `key` using `((GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev D ψ hψ θ hθ S T d g hg).2 M hM hMf).2`. Establish `hmemM : ∀ t, heisO ψ S T (M t) g ∈ GlobalTheory.Size.thetaLevel ψ S T U` using `fun t => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (M t), fun u hu h0 => GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)⟩`.

Establish `hmemg : g ∈ GlobalTheory.Size.thetaLevel ψ S T U` using `⟨hg, hUl⟩`. Establish `hmemd : GlobalTheory.OrientedHeis.dLine ψ S T M g ∈ GlobalTheory.Size.thetaLevel ψ S T U`. Use `⟨GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hg, fun u hu h0 => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Establish `: (fun t => heisO ψ S T (M t) g p) = fun t => heisO ψ S T u (heisO ψ S T (M t) g) p`.

Use function extensionality and compare the values at `t`. Rewrite using `[GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)]`. Use `conv_rhs => unfold GlobalTheory.OrientedHeis.dLine`. Rewrite using `[this]`. Unfold `GlobalTheory.OrientedHeis.dLine`.

Rewrite using `[heisO, ← deriv_const_mul_field]`. Both sides reduce to the same expression. Establish `hG : HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) (ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0`. Rewrite using `[hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff, tendsto_iff_edist_tendsto_0]`. Establish `hφ : ∀ t : ℝ, (t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g ∈ GlobalTheory.Size.thetaLevel ψ S T U` using `fun t => Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)) hmemd`.

Establish `he : ∀ t : ℝ, edist (slope (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) 0 t - ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0 = ‖ℓ ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g)‖ₑ`. Introduce `t`. Rewrite using `[edist_zero_right, lsub _ _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)).1 hmemd.1, hℓ.smul _ _ (Submodule.sub_mem _ (hmemM t) hmemg).1, lsub _ _ (hmemM t).1 hg, slope_def_module, sub_zero, M.map_zero, GlobalTheory.WeilVacMove.heisO_zero, Complex.real_smul, Comp …`. Repeatedly rewrite using `[he]`. Establish `hT : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * supSob ψ θ d ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g)) (nhdsWithin 0 {0}ᶜ) (nhds 0)`.

Use `ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) key (Or.inr ENNReal.coe_ne_top)` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Then use the resulting hypothesis. Conclude with `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le) (fun t => hC _ (hφ t))`. Use `set f' : WO S T → ℂ := fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0 with hf'_def`. Establish `hf'θ : IsThetaFunO ψ S T f'` using `GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hf`.

Establish `hdl : GlobalTheory.OrientedHeis.dLine ψ S T M g = heisO ψ S T w f' - (2 * deriv c 0) • g`. Use function extensionality and compare the values at `p`. Use `set H : ℝ → ℂ := fun s => heisO ψ S T w (heisO ψ S T (M s) f) p with hH_def`. Establish `hHd : HasDerivAt H (heisO ψ S T w f' p) 0`. Establish `hd` using `(GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL hf (p + w) 0).differentiableAt.hasDerivAt`.

Conclude with `hd.const_mul (ψ (symplOH S T p w))`. Establish `hH0 : H 0 = g p` using `by show heisO ψ S T w (heisO ψ S T (M 0) f) p = heisO ψ S T w f p`. Rewrite using `[M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]`. Establish `hEq : (fun s : ℝ => heisO ψ S T (M s) g p) = fun s => (c s)⁻¹ * ((c s)⁻¹ * H s)`. Use function extensionality and compare the values at `s`.

Establish `e1 : H s = c s * heisO ψ S T (w + M s) f p` using `by show heisO ψ S T w (heisO ψ S T (M s) f) p = _`. Rewrite using `[GlobalTheory.OrientedHeis.heisO_heisO]`. Both sides reduce to the same expression. Rewrite using `[e1, hF s, Pi.smul_apply, smul_eq_mul]`. Clear denominators, using `[hcne s]` for the nonvanishing conditions.

Establish `hci` using `hcd.inv (by rw [hc0]; exact one_ne_zero)`. Establish `hD` using `hci.mul (hci.mul hHd)`. Establish `hD' : HasDerivAt (fun s : ℝ => heisO ψ S T (M s) g p) _ 0` using `hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => congrFun hEq s)`. Use `show deriv (fun s : ℝ => heisO ψ S T (M s) g p) 0 = _`. Rewrite using `[hD'.deriv]`.

Simplify using `only [Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc0, hH0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfun : (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) = fun s => c s * ℓ (heisO ψ S T (M s) g)`. Use function extensionality and compare the values at `s`. Rewrite using `[hF s, hℓ.smul _ _ (hmemM s).1]`.

Rewrite using `[hfun]`. Establish `hP` using `hcd.mul hG`. Use `hP.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[hdl, lsub _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf'θ w) (GlobalTheory.OrientedHeis.theta_smul _ hg), hℓ.smul _ _ hg, hc0]`. Simplify using `only [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_form_heisO_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∀ w : WO S T, HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) (ℓ (heisO ψ S T w (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0)) - deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 * ℓ (heisO ψ S T w f)) 0 := by
  intro D ψ hψ θ hθ S T ℓ hℓ f hf M hM hMf w
  have hL : IsRealDir T S M := ⟨hM, hMf⟩
  have hg : IsThetaFunO ψ S T (heisO ψ S T w f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  set g := heisO ψ S T w f with hg_def
  set c : ℝ → ℂ := fun s => ψ (symplOH S T w (M s)) with hc_def

  have lsub : ∀ a b, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b → ℓ (a - b) = ℓ a - ℓ b := by
    intro a b ha hb
    have := hℓ.add (a - b) b (GlobalTheory.OrientedHeis.theta_sub ha hb) hb
    rw [sub_add_cancel] at this
    rw [this]; ring

  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hce : c = fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) *
      (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1))))) := by
    funext s
    show ψ (symplOH S T w (M s)) = _
    rw [(smooth_iff_sm_and_real_lines D θ σ h T S).2.1 M hL s, GlobalTheory.OrientedHeis.psi_symplOH h hψ, map_smul]
    rfl
  have hcd : HasDerivAt c (deriv c 0) 0 := by
    refine DifferentiableAt.hasDerivAt ?_
    have h2 : ContDiff ℝ ∞ fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) *
        (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1))))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (contDiff_id.mul contDiff_const)))
    rw [hce]
    exact h2.differentiable (by simp) 0
  have hc0 : c 0 = 1 := by
    show ψ (symplOH S T w (M 0)) = 1
    rw [M.map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, ψ.map_zero_eq_one]
  have hcne : ∀ s, c s ≠ 0 := by
    intro s; rw [hce]; exact Complex.exp_ne_zero _

  have hF : ∀ s, heisO ψ S T (w + M s) f = c s • heisO ψ S T (M s) g := by
    intro s
    rw [hg_def, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul,
      GlobalTheory.FinTranslate.symplOH_skew (S := S) (T := T) w (M s), add_neg_cancel, ψ.map_zero_eq_one, one_smul, add_comm]

  obtain ⟨U, hUo, hUl⟩ := hg.level
  obtain ⟨d, C, hC⟩ := hℓ.bound U hUo
  have key := ((GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev D ψ hψ θ hθ S T d g hg).2 M hM hMf).2
  have hmemM : ∀ t, heisO ψ S T (M t) g ∈ GlobalTheory.Size.thetaLevel ψ S T U := fun t =>
    ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (M t),
      fun u hu h0 => GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)⟩
  have hmemg : g ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hg, hUl⟩
  have hmemd : GlobalTheory.OrientedHeis.dLine ψ S T M g ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
    refine ⟨GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hg, fun u hu h0 => ?_⟩
    funext p
    have : (fun t => heisO ψ S T (M t) g p) = fun t => heisO ψ S T u (heisO ψ S T (M t) g) p := by
      funext t; rw [GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)]
    conv_rhs => unfold GlobalTheory.OrientedHeis.dLine; rw [this]
    unfold GlobalTheory.OrientedHeis.dLine
    rw [heisO, ← deriv_const_mul_field]
    rfl
  have hG : HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) (ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff, tendsto_iff_edist_tendsto_0]
    have hφ : ∀ t : ℝ, (t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g ∈
        GlobalTheory.Size.thetaLevel ψ S T U := fun t =>
      Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)) hmemd
    have he : ∀ t : ℝ, edist (slope (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) 0 t - ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0
        = ‖ℓ ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g)‖ₑ := by
      intro t
      rw [edist_zero_right, lsub _ _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)).1 hmemd.1,
        hℓ.smul _ _ (Submodule.sub_mem _ (hmemM t) hmemg).1, lsub _ _ (hmemM t).1 hg, slope_def_module,
        sub_zero, M.map_zero, GlobalTheory.WeilVacMove.heisO_zero, Complex.real_smul, Complex.ofReal_inv]
    simp_rw [he]
    have hT : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * supSob ψ θ d ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) -
        GlobalTheory.OrientedHeis.dLine ψ S T M g)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) key (Or.inr ENNReal.coe_ne_top)
      rwa [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le)
      (fun t => hC _ (hφ t))

  set f' : WO S T → ℂ := fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0 with hf'_def
  have hf'θ : IsThetaFunO ψ S T f' := GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hf
  have hdl : GlobalTheory.OrientedHeis.dLine ψ S T M g = heisO ψ S T w f' - (2 * deriv c 0) • g := by
    funext p
    set H : ℝ → ℂ := fun s => heisO ψ S T w (heisO ψ S T (M s) f) p with hH_def
    have hHd : HasDerivAt H (heisO ψ S T w f' p) 0 := by
      have hd := (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL hf (p + w) 0).differentiableAt.hasDerivAt
      exact hd.const_mul (ψ (symplOH S T p w))
    have hH0 : H 0 = g p := by
      show heisO ψ S T w (heisO ψ S T (M 0) f) p = heisO ψ S T w f p
      rw [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]
    have hEq : (fun s : ℝ => heisO ψ S T (M s) g p) = fun s => (c s)⁻¹ * ((c s)⁻¹ * H s) := by
      funext s
      have e1 : H s = c s * heisO ψ S T (w + M s) f p := by
        show heisO ψ S T w (heisO ψ S T (M s) f) p = _
        rw [GlobalTheory.OrientedHeis.heisO_heisO]; rfl
      rw [e1, hF s, Pi.smul_apply, smul_eq_mul]
      field_simp [hcne s]
    have hci := hcd.inv (by rw [hc0]; exact one_ne_zero)
    have hD := hci.mul (hci.mul hHd)
    have hD' : HasDerivAt (fun s : ℝ => heisO ψ S T (M s) g p) _ 0 :=
      hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => congrFun hEq s)
    show deriv (fun s : ℝ => heisO ψ S T (M s) g p) 0 = _
    rw [hD'.deriv]
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc0, hH0]
    ring

  have hfun : (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) = fun s => c s * ℓ (heisO ψ S T (M s) g) := by
    funext s
    rw [hF s, hℓ.smul _ _ (hmemM s).1]
  rw [hfun]
  have hP := hcd.mul hG
  refine hP.congr_deriv ?_
  rw [hdl, lsub _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf'θ w) (GlobalTheory.OrientedHeis.theta_smul _ hg),
    hℓ.smul _ _ hg, hc0]
  simp only [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  ring

end GlobalTheory.MatCoeffDeriv
