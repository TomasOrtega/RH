import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitianStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ContDiff ComplexOrder BoundedContinuousFunction

namespace GlobalTheory.RealWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def toB (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) : BB ψ S T :=
  mkB f hf.cont (theta_bounded hψ hf) hf.quasi

/- English proof (translation)
The claim follows from `coe_mkB _ _ _ _`.
-/
theorem coe_toB (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) :
    ((toB hψ f hf).1 : WO S T → ℂ) = f := coe_mkB _ _ _ _

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' := fun a _ hf => theta_smul a hf

/- English proof (translation)
The claim follows from `Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO S T w)).contDiff))`.
-/
theorem contDiff_phase (c : ℂ) (w : RW T S) :
    ContDiff ℝ ∞ fun x : RW T S => Complex.exp (c * (GlobalTheory.OrientedHeis.omO S T w x : ℝ)) :=
  Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO S T w)).contDiff))

/- English proof (translation)
Use `⟨F.2, hl, F.1.continuous, ((smooth_iff_sm_and_real_lines D θ σ h T S).1 _).2 fun w => ?_⟩` and prove the remaining obligations. Establish `h1 : ContDiff ℝ ∞ fun x : RW T S => ev _ _ w (rhoV hψ σ S T (vecL x) F)` using `((ev _ _ w).restrictScalars ℝ).contDiff.comp (ContDiff.comp hF (vecL (O := D.what₂.Tau) (m := T.rank) (n := S.rank)).contDiff)`. Establish `h2` using `(contDiff_phase (Real.pi * Complex.I) (piW θ T S w)).mul h1`. Use `(congrArg (ContDiff ℝ ∞) (funext fun x => ?_)).mp h2` and prove the remaining obligations. Rewrite using `[ev_apply, coe_rhoV]`.

Unfold `iotaV`. Rewrite using `[unv_vecL, heisO_iota h hψ, ← mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]`.
-/
theorem theta_of_sm (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F)
    (hl : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u F.1 = F.1) : IsThetaFunO ψ S T F.1 := by
  refine ⟨F.2, hl, F.1.continuous, ((smooth_iff_sm_and_real_lines D θ σ h T S).1 _).2 fun w => ?_⟩
  have h1 : ContDiff ℝ ∞ fun x : RW T S => ev _ _ w (rhoV hψ σ S T (vecL x) F) :=
    ((ev _ _ w).restrictScalars ℝ).contDiff.comp
      (ContDiff.comp hF (vecL (O := D.what₂.Tau) (m := T.rank) (n := S.rank)).contDiff)
  have h2 := (contDiff_phase (Real.pi * Complex.I) (piW θ T S w)).mul h1
  refine (congrArg (ContDiff ℝ ∞) (funext fun x => ?_)).mp h2
  rw [ev_apply, coe_rhoV]
  unfold iotaV
  rw [unv_vecL, heisO_iota h hψ, ← mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

/- English proof (translation)
Establish `h1` using `((contDiff_phase (-(Real.pi * Complex.I)) (piW θ T S w)).mul (theta_sm h hF w)).comp (unvecL (O := D.what₂.Tau) (m := T.rank) (n := S.rank)).contDiff`. Establish `e : (fun v => ev _ _ w (rhoV hψ σ S T v F)) = _` using `funext fun v => (congrFun (coe_rhoV hψ v F) w).trans (heisO_iota h hψ (unvecL v) F.1 w)`. Rewrite using `[e]`. Conclude with `h1.differentiable (by simp)`.
-/
theorem differentiable_ev (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1)
    (w : WO S T) : Differentiable ℝ fun v => ev _ _ w (rhoV hψ σ S T v F) := by
  have h1 := ((contDiff_phase (-(Real.pi * Complex.I)) (piW θ T S w)).mul (theta_sm h hF w)).comp
    (unvecL (O := D.what₂.Tau) (m := T.rank) (n := S.rank)).contDiff
  have e : (fun v => ev _ _ w (rhoV hψ σ S T v F)) = _ := funext fun v =>
    (congrFun (coe_rhoV hψ v F) w).trans (heisO_iota h hψ (unvecL v) F.1 w)
  rw [e]
  exact h1.differentiable (by simp)

/- English proof (translation)
Take `⟨L, hL, e⟩` from `(smooth_iff_sm_and_real_lines D θ σ h T S).2.2 (unvecL z)`. Establish `h1` using `theta_dLine h.inf hψ hL hF`. Use `⟨toB hψ _ h1, by rw [coe_toB]; exact h1, fun w => ?_⟩` and prove the remaining obligations. Establish `h2` using `hasDerivAt_heisO h.inf hψ hL hF w 0`. Rewrite `h2` using `[L.map_zero, heisO_zero]`.

Rewrite using `[ev_apply, coe_toB]`. Use `h2 using 2 with t` and compare the differences between its conclusion and the goal. Rewrite using `[ev_apply, coe_rhoV, e]`. Unfold `iotaV`. Rewrite using `[map_smul]`.
-/
theorem exists_deriv (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1)
    (z : Ix S T → ℂ) : ∃ F' : BB ψ S T, IsThetaFunO ψ S T F'.1 ∧ ∀ w,
      HasDerivAt (fun t : ℝ => ev _ _ w (rhoV hψ σ S T (t • z) F)) (ev _ _ w F') 0 := by
  obtain ⟨L, hL, e⟩ := (smooth_iff_sm_and_real_lines D θ σ h T S).2.2 (unvecL z)
  have h1 := theta_dLine h.inf hψ hL hF
  refine ⟨toB hψ _ h1, by rw [coe_toB]; exact h1, fun w => ?_⟩
  have h2 := hasDerivAt_heisO h.inf hψ hL hF w 0
  rw [L.map_zero, heisO_zero] at h2
  rw [ev_apply, coe_toB]
  convert h2 using 2 with t
  rw [ev_apply, coe_rhoV, e]
  unfold iotaV
  rw [map_smul]

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun v => rhoV hψ σ S T v F) (fderiv ℝ (fun v => rhoV hψ σ S T v F) 0) ((0 : ℝ) • z)`. Rewrite using `[zero_smul]`. Conclude with `(ContDiff.differentiable hF (by simp) 0).hasFDerivAt`. Establish `h2 : HasDerivAt (fun t : ℝ => t • z) z 0` using `by simpa using (hasDerivAt_id (0 : ℝ)).smul_const z`. Establish `h3` using `((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h1.comp_hasDerivAt (0 : ℝ) h2)`.

Conclude with `h3.deriv.symm`.
-/
theorem ev_fderiv (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F) (z : Ix S T → ℂ) (w : WO S T) :
    ev _ _ w (fderiv ℝ (fun v => rhoV hψ σ S T v F) 0 z) =
      deriv (fun t : ℝ => heisO ψ S T (iotaV σ S T (t • z)) F.1 w) 0 := by
  have h1 : HasFDerivAt (fun v => rhoV hψ σ S T v F) (fderiv ℝ (fun v => rhoV hψ σ S T v F) 0)
      ((0 : ℝ) • z) := by
    rw [zero_smul]
    exact (ContDiff.differentiable hF (by simp) 0).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => t • z) z 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h1.comp_hasDerivAt (0 : ℝ) h2)
  exact h3.deriv.symm

open Classical in

/- English proof (translation)
Generalize the expression as in `hA : fderiv ℝ (fun v => rhoV hψ σ S T v F) 0 = A`. Establish `h1 : ∀ τ (y : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T), ev _ _ w (A (vecL (Pi.single τ y : RW T S))) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ y F.1 w`. Introduce `τ y w`. Rewrite using `[← hA, ev_fderiv hψ F hF]`. Establish `e : ∀ t : ℝ, iotaV σ S T (t • vecL (Pi.single τ y : RW T S)) = lineAt θ τ y t` using `fun t => by`.

Rewrite using `[GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ y t]`. Both sides reduce to the same expression. Simplify using `only [e]`. Both sides reduce to the same expression. Establish `h2 : ∀ x : Ix S T → ℂ, x = ∑ τ, vecL (Pi.single τ (cpt x τ) : RW T S)`.

Introduce `x`. Rewrite using `[← map_sum]`. Conclude with `(congrArg vecL (Finset.univ_sum_single (unvecL x))).symm`. Establish `h3 : ∀ τ, cpt (Complex.I • blk sT sS *ᵥ z) τ = cplxO (sS τ) (sT τ) (cpt z τ)` using `fun τ => by`. Unfold `cplxO`.

Rewrite using `[← cpt_blk]`. Both sides reduce to the same expression. Establish `h4 : ∀ x : Ix S T → ℂ, A x = ∑ τ, A (vecL (Pi.single τ (cpt x τ) : RW T S))` using `fun x => (congrArg A (h2 x)).trans (map_sum A _ _)`. Rewrite using `[h4 z, h4 (Complex.I • blk sT sS *ᵥ z), Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun τ _ => QB_ext fun w => ?_` and prove the remaining obligations.

Rewrite using `[← ev_apply, map_add, map_smul, h1, h1, h3]`. Conclude with `congrFun (hv τ (cpt z τ)) w`.
-/
theorem fderiv_vac (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) F.1) (z : Ix S T → ℂ) :
    fderiv ℝ (fun v => rhoV hψ σ S T v F) 0 z +
      Complex.I • fderiv ℝ (fun v => rhoV hψ σ S T v F) 0 (Complex.I • blk sT sS *ᵥ z) = 0 := by
  generalize hA : fderiv ℝ (fun v => rhoV hψ σ S T v F) 0 = A
  have h1 : ∀ τ (y : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T),
      ev _ _ w (A (vecL (Pi.single τ y : RW T S))) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ y F.1 w := by
    intro τ y w
    rw [← hA, ev_fderiv hψ F hF]
    have e : ∀ t : ℝ, iotaV σ S T (t • vecL (Pi.single τ y : RW T S)) = lineAt θ τ y t := fun t => by
      rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ y t]
      rfl
    simp only [e]
    rfl
  have h2 : ∀ x : Ix S T → ℂ, x = ∑ τ, vecL (Pi.single τ (cpt x τ) : RW T S) := by
    intro x
    rw [← map_sum]
    exact (congrArg vecL (Finset.univ_sum_single (unvecL x))).symm
  have h3 : ∀ τ, cpt (Complex.I • blk sT sS *ᵥ z) τ = cplxO (sS τ) (sT τ) (cpt z τ) := fun τ => by
    unfold cplxO
    rw [← cpt_blk]
    rfl
  have h4 : ∀ x : Ix S T → ℂ, A x = ∑ τ, A (vecL (Pi.single τ (cpt x τ) : RW T S)) :=
    fun x => (congrArg A (h2 x)).trans (map_sum A _ _)
  rw [h4 z, h4 (Complex.I • blk sT sS *ᵥ z), Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun τ _ => QB_ext fun w => ?_
  rw [← ev_apply, map_add, map_smul, h1, h1, h3]
  exact congrFun (hv τ (cpt z τ)) w

/- English proof (translation)
Rewrite using `[(ENNReal.pow_right_strictMono two_ne_zero).injective.eq_iff, enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_inj, ← NNReal.coe_inj, coe_nnnorm, coe_nnnorm]`.
-/
theorem enorm_sq_inj {E : Type} [NormedAddCommGroup E] {a b : E} : ‖a‖ₑ ^ 2 = ‖b‖ₑ ^ 2 ↔ ‖a‖ = ‖b‖ := by
  rw [(ENNReal.pow_right_strictMono two_ne_zero).injective.eq_iff, enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_inj,
    ← NNReal.coe_inj, coe_nnnorm, coe_nnnorm]

/- English proof (translation)
Take `⟨-, i2, i3, i4, i5, K, hK, hc⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Use `haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `hfin` using `GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hc μ h𝓕`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩`.

Establish `key : ∀ G : BB ψ S T, ∫⁻ w in 𝓕, ‖G.1 w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ w in 𝓕, ‖G.1 w‖ ^ 2 ∂μ)`. Introduce `G`. Rewrite using `[ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall fun w => by positivity)]`. Simplify using `only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Conclude with `Integrable.of_bound (G.1.continuous.norm.pow 2).aestronglyMeasurable (‖G‖ ^ 2) (Filter.Eventually.of_forall fun w => by`.

Rewrite using `[norm_pow, norm_norm]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (norm_ev_le w G) 2)`. Rewrite using `[key, key, coe_rhoB]`. Simplify using `only [GlobalTheory.HeisOrtho.norm_heisO hψ.1]`. Rewrite using `[GlobalTheory.HeisOrtho.setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕 (fun w => ‖F.1 w‖ ^ 2) (fun γ hγ w => by rw [BB_norm_periodic hψ F γ hγ]) u]`.
-/
theorem lintegral_rhoB (hψ : IsStdChar D ψ (-1)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (u : WO S T) (F : BB ψ S T) :
    ∫⁻ w in 𝓕, ‖(rhoB hψ u F).1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖F.1 w‖ₑ ^ 2 ∂μ := by
  obtain ⟨-, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hc μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have key : ∀ G : BB ψ S T, ∫⁻ w in 𝓕, ‖G.1 w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ w in 𝓕, ‖G.1 w‖ ^ 2 ∂μ) := by
    intro G
    rw [ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall fun w => by positivity)]
    · simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    · exact Integrable.of_bound (G.1.continuous.norm.pow 2).aestronglyMeasurable (‖G‖ ^ 2)
        (Filter.Eventually.of_forall fun w => by
          rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_ev_le w G) 2)
  rw [key, key, coe_rhoB]
  simp only [GlobalTheory.HeisOrtho.norm_heisO hψ.1]
  rw [GlobalTheory.HeisOrtho.setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕 (fun w => ‖F.1 w‖ ^ 2)
    (fun γ hγ w => by rw [BB_norm_periodic hψ F γ hγ]) u]

/- English proof (translation)
Take `⟨C, hC⟩` from `Θ.exists_isCompl`. Set `p` to `Θ.linearProjOfIsCompl C hC`. Establish `hp : ∀ f : Θ, p f = f` using `Submodule.linearProjOfIsCompl_apply_left hC`. Use `⟨{ toFun := fun g => Θ.subtype ∘ₗ (om g - 1) ∘ₗ p + 1, map_one' := by simp, map_mul' := fun g g' => ?_ }, fun g f => by simp [hp]⟩` and prove the remaining obligations. Use extensionality with `f`.

Simplify using `[hp]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_extend {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (Θ : Submodule ℂ M)
    (om : G →* Module.End ℂ Θ) : ∃ om' : G →* Module.End ℂ M, ∀ g (f : Θ), om' g f = om g f := by
  obtain ⟨C, hC⟩ := Θ.exists_isCompl
  let p := Θ.linearProjOfIsCompl C hC
  have hp : ∀ f : Θ, p f = f := Submodule.linearProjOfIsCompl_apply_left hC
  refine ⟨{ toFun := fun g => Θ.subtype ∘ₗ (om g - 1) ∘ₗ p + 1, map_one' := by simp, map_mul' := fun g g' => ?_ },
    fun g f => by simp [hp]⟩
  ext f
  simp [hp]
  abel

/- English proof (translation)
Set `B₀ : (Ix S T → ℂ) →ₗ[ℝ] (Ix S T → ℂ) →ₗ[ℝ] ℝ` to `-(GlobalTheory.VacUnique.omO S T).compl₁₂ unvecL.toLinearMap unvecL.toLinearMap`. Set `om : (Ix S T → ℂ) →L[ℝ] (Ix S T → ℂ) →L[ℝ] ℝ` to `LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap ∘ₗ B₀)`. Establish `e : (fun x y => om x y) = fun x y => (star y ⬝ᵥ HM S T *ᵥ x).im`. Use function extensionality and compare the values at `x y`. Rewrite using `[im_HM x y]`.

Both sides reduce to the same expression. Establish `hH : IsHeis (fun x y => om x y) (rhoV hψ σ S T)` using `e ▸ isHeis_rhoB h hψ`. Conclude with `GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set _ _ om _ hH (WO S T) (ev _ _) norm_ev_le (fun b C => norm_QB_le b) (fun x v => ⟨ψ (symplOH S T x (iotaV σ S T v)), x + iotaV σ S T v, fun b => congrFun (coe_rhoV hψ v b) x⟩) {F | IsThetaFunO ψ S T F.1} (differentiable …`.
-/
theorem sm_of_theta (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1) :
    GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F := by
  let B₀ : (Ix S T → ℂ) →ₗ[ℝ] (Ix S T → ℂ) →ₗ[ℝ] ℝ := -(GlobalTheory.VacUnique.omO S T).compl₁₂ unvecL.toLinearMap unvecL.toLinearMap
  let om : (Ix S T → ℂ) →L[ℝ] (Ix S T → ℂ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap ∘ₗ B₀)
  have e : (fun x y => om x y) = fun x y => (star y ⬝ᵥ HM S T *ᵥ x).im := by
    funext x y
    rw [im_HM x y]
    rfl
  have hH : IsHeis (fun x y => om x y) (rhoV hψ σ S T) := e ▸ isHeis_rhoB h hψ
  exact GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set _ _ om _ hH (WO S T) (ev _ _) norm_ev_le (fun b C => norm_QB_le b)
    (fun x v => ⟨ψ (symplOH S T x (iotaV σ S T v)), x + iotaV σ S T v, fun b => congrFun (coe_rhoV hψ v b) x⟩)
    {F | IsThetaFunO ψ S T F.1} (differentiable_ev h hψ) (exists_deriv h hψ) F hF

/- English proof (translation)
Unfold `rhoV`. Rewrite using `[rhoB_rhoB, rhoB_rhoB, (symplOH_fin_real hu (real_iotaV h v)).1, (symplOH_fin_real hu (real_iotaV h v)).2, add_comm]`.
-/
theorem rhoB_comm (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (hu : u.map (infPart D) = 0) (v : Ix S T → ℂ)
    (F : BB ψ S T) : rhoB hψ u (rhoV hψ σ S T v F) = rhoV hψ σ S T v (rhoB hψ u F) := by
  unfold rhoV
  rw [rhoB_rhoB, rhoB_rhoB, (symplOH_fin_real hu (real_iotaV h v)).1, (symplOH_fin_real hu (real_iotaV h v)).2, add_comm]

/- English proof (translation)
Unfold `rhoV`. Rewrite using `[rhoB_rhoB, (symplOH_fin_real hu (real_iotaV h v)).1, AddChar.map_zero_eq_one, one_smul]`.
-/
theorem rhoB_add (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (hu : u.map (infPart D) = 0) (v : Ix S T → ℂ)
    (F : BB ψ S T) : rhoB hψ (u + iotaV σ S T v) F = rhoB hψ u (rhoV hψ σ S T v F) := by
  unfold rhoV
  rw [rhoB_rhoB, (symplOH_fin_real hu (real_iotaV h v)).1, AddChar.map_zero_eq_one, one_smul]

/- English proof (translation)
Use `⟨w - iotaV σ S T (vecL (piW θ T S w)), vecL (piW θ T S w), ?_, (sub_add_cancel _ _).symm⟩` and prove the remaining obligations. Establish `hp : piW θ T S (w - iotaV σ S T (vecL (piW θ T S w))) = 0`. Unfold `iotaV`. Rewrite using `[unv_vecL, AddMonoidHom.map_sub, h.pi_iota, sub_self]`. Use extensionality with `i j`.

Conclude with `ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j`.
-/
theorem exists_parts (h : Chart θ σ) (w : WO S T) :
    ∃ (u : WO S T) (v : Ix S T → ℂ), u.map (infPart D) = 0 ∧ w = u + iotaV σ S T v := by
  refine ⟨w - iotaV σ S T (vecL (piW θ T S w)), vecL (piW θ T S w), ?_, (sub_add_cancel _ _).symm⟩
  have hp : piW θ T S (w - iotaV σ S T (vecL (piW θ T S w))) = 0 := by
    unfold iotaV
    rw [unv_vecL, AddMonoidHom.map_sub, h.pi_iota, sub_self]
  ext i j
  exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j

/- English proof (translation)
Establish `ht : ∀ f : thetaSub ψ S T, IsThetaFunO ψ S T (toB hψ f.1 f.2).1` using `fun f => (coe_toB hψ f.1 f.2).symm ▸ f.2`. Establish `hb : ∀ (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1), toB hψ F.1 hF = F` using `fun F hF => QB_ext fun x => congrFun (coe_toB hψ _ hF) x`. Set `w : G → Module.End ℂ (thetaSub ψ S T)` to `fun p => { toFun := fun f => ⟨(Ω p (toB hψ f.1 f.2)).1, hth p _ (ht f)⟩ map_add' := fun f g => by`. Establish `e : toB hψ (f + g).1 (f + g).2 = toB hψ f.1 f.2 + toB hψ g.1 g.2` using `QB_ext fun x => rfl`. Use `Subtype.ext ?_` and prove the remaining obligations.

Simplify using `only [e, hadd p _ _ (ht f) (ht g)]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun a f => by`. Establish `e : toB hψ (a • f).1 (a • f).2 = a • toB hψ f.1 f.2` using `QB_ext fun x => rfl`. Use `Subtype.ext ?_` and prove the remaining obligations.

Simplify using `only [e, hsmul p a _ (ht f)]`. Use `rfl }`. Establish `hw : ∀ p f, (w p f).1 = (Ω p (toB hψ f.1 f.2)).1` using `fun _ _ => rfl`. Set `w' : G →* Module.End ℂ (thetaSub ψ S T)` to `{ toFun := w map_one' := LinearMap.ext fun f => Subtype.ext (by rw [hw, hone _ (ht f)]; exact coe_toB hψ f.1 f.2) map_mul' := fun p p' => LinearMap.ext fun f => Subtype.ext (by`. Rewrite using `[hw, hmul _ _ _ (ht f), Module.End.mul_apply, hw]`.

Conclude with `congrArg (fun F : BB ψ S T => ((Ω p F).1 : WO S T → ℂ)) (hb _ (hth p' _ (ht f))).symm) }`. Take `⟨om, hom⟩` from `exists_extend (thetaSub ψ S T) w'`. Use `⟨om, fun p F hF => (hom p ⟨F.1, hF⟩).trans ((hw p ⟨F.1, hF⟩).trans ?_)⟩` and prove the remaining obligations. Conclude with `congrArg (fun F : BB ψ S T => ((Ω p F).1 : WO S T → ℂ)) (hb F hF)`.
-/
theorem exists_hom (hψ : IsStdChar D ψ (-1)) {G : Type} [Group G] (Ω : G → BB ψ S T → BB ψ S T)
    (hth : ∀ p F, IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (Ω p F).1)
    (hadd : ∀ p F F', IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T F'.1 → Ω p (F + F') = Ω p F + Ω p F')
    (hsmul : ∀ p (a : ℂ) F, IsThetaFunO ψ S T F.1 → Ω p (a • F) = a • Ω p F)
    (hone : ∀ F, IsThetaFunO ψ S T F.1 → Ω 1 F = F)
    (hmul : ∀ p p' F, IsThetaFunO ψ S T F.1 → Ω (p * p') F = Ω p (Ω p' F)) :
    ∃ om : G →* Module.End ℂ (WO S T → ℂ), ∀ p F, IsThetaFunO ψ S T F.1 → om p F.1 = (Ω p F).1 := by
  have ht : ∀ f : thetaSub ψ S T, IsThetaFunO ψ S T (toB hψ f.1 f.2).1 := fun f => (coe_toB hψ f.1 f.2).symm ▸ f.2
  have hb : ∀ (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1), toB hψ F.1 hF = F :=
    fun F hF => QB_ext fun x => congrFun (coe_toB hψ _ hF) x
  let w : G → Module.End ℂ (thetaSub ψ S T) := fun p =>
    { toFun := fun f => ⟨(Ω p (toB hψ f.1 f.2)).1, hth p _ (ht f)⟩
      map_add' := fun f g => by
        have e : toB hψ (f + g).1 (f + g).2 = toB hψ f.1 f.2 + toB hψ g.1 g.2 := QB_ext fun x => rfl
        refine Subtype.ext ?_
        simp only [e, hadd p _ _ (ht f) (ht g)]
        rfl
      map_smul' := fun a f => by
        have e : toB hψ (a • f).1 (a • f).2 = a • toB hψ f.1 f.2 := QB_ext fun x => rfl
        refine Subtype.ext ?_
        simp only [e, hsmul p a _ (ht f)]
        rfl }
  have hw : ∀ p f, (w p f).1 = (Ω p (toB hψ f.1 f.2)).1 := fun _ _ => rfl
  let w' : G →* Module.End ℂ (thetaSub ψ S T) :=
    { toFun := w
      map_one' := LinearMap.ext fun f => Subtype.ext (by rw [hw, hone _ (ht f)]; exact coe_toB hψ f.1 f.2)
      map_mul' := fun p p' => LinearMap.ext fun f => Subtype.ext (by
        rw [hw, hmul _ _ _ (ht f), Module.End.mul_apply, hw]
        exact congrArg (fun F : BB ψ S T => ((Ω p F).1 : WO S T → ℂ)) (hb _ (hth p' _ (ht f))).symm) }
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T) w'
  refine ⟨om, fun p F hF => (hom p ⟨F.1, hF⟩).trans ((hw p ⟨F.1, hF⟩).trans ?_)⟩
  exact congrArg (fun F : BB ψ S T => ((Ω p F).1 : WO S T → ℂ)) (hb F hF)

/- English proof (translation)
Take `⟨-, i2, i3, i4, i5, K, hK, hc⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Use `haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `hlt` using `GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hc μ h𝓕`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩`.

Rewrite using `[lintegral_norm_sq_eq_toL2, lintegral_norm_sq_eq_toL2, enorm_sq_inj]`. Use `hn _ (toL2 _ _ (μ.restrict 𝓕)) fun v G => ?_` and prove the remaining obligations. Rewrite using `[← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]`. Conclude with `lintegral_rhoB hψ μ 𝓕 hμ h𝓕 _ G`.
-/
theorem lintegral_eq_of_norms (hψ : IsStdChar D ψ (-1)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {F F' : BB ψ S T}
    (hn : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : BB ψ S T →L[ℂ] H),
      (∀ w G, ‖Φ (rhoB hψ w G)‖ = ‖Φ G‖) → ‖Φ F'‖ = ‖Φ F‖) :
    ∫⁻ w in 𝓕, ‖F'.1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖F.1 w‖ₑ ^ 2 ∂μ := by
  obtain ⟨-, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hlt := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hc μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  rw [lintegral_norm_sq_eq_toL2, lintegral_norm_sq_eq_toL2, enorm_sq_inj]
  refine hn _ (toL2 _ _ (μ.restrict 𝓕)) fun v G => ?_
  rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
  exact lintegral_rhoB hψ μ 𝓕 hμ h𝓕 _ G

open Classical in
/- English proof (translation)
Rewrite using `[mM_apply, blk_mul, blk_mul]`. Apply the tactic sequence `congr 1 <;> funext τ`. Conclude with `cT τ`. Establish `h1` using `GlobalTheory.WeilVacMove.compAt_mt_mul_inv θ τ S g`. Establish `h2` using `GlobalTheory.WeilVacMove.compAt_mt_inv_mul θ τ S g`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]`. Use `_ = _ := by rw [cS τ, ← Matrix.mul_assoc, h2, Matrix.one_mul]`.
-/
theorem blk_comm_mM {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {g : GA D S} {k : GA D T}
    (cS : ∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ)
    (cT : ∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T k) = compAt θ τ (Formalism.L2.Theta.mt T k) * sT τ) :
    blk sT sS * mM θ S T (g, k) = mM θ S T (g, k) * blk sT sS := by
  rw [mM_apply, blk_mul, blk_mul]
  congr 1 <;> funext τ
  · exact cT τ
  · have h1 := GlobalTheory.WeilVacMove.compAt_mt_mul_inv θ τ S g
    have h2 := GlobalTheory.WeilVacMove.compAt_mt_inv_mul θ τ S g
    calc _ = compAt θ τ (Formalism.L2.Theta.mt S g⁻¹) * (sS τ * compAt θ τ (Formalism.L2.Theta.mt S g)) *
          compAt θ τ (Formalism.L2.Theta.mt S g⁻¹) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = _ := by rw [cS τ, ← Matrix.mul_assoc, h2, Matrix.one_mul]

open Classical in
/- English proof (translation)
Rewrite using `[mM_apply]`. Conclude with `detPlus_blockDiagonal _ _ _ _`.
-/
theorem detPlus_pairMatrix (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (g : GA D S) (k : GA D T) :
    dP (blk sT sS) (mM θ S T (g, k)) = ∏ τ, GlobalTheory.WeilParts.detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹))
      (compAt θ τ (Formalism.L2.Theta.mt T k)) := by
  rw [mM_apply]
  exact detPlus_blockDiagonal _ _ _ _

open Classical in

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Take `⟨Ω, ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩, htriv, hcont, hvac⟩` from `GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian (Ix S T) (HM S T) HM_herm HM_det (BB ψ S T) (rhoV hψ σ S T) (isHeis_rhoB h hψ) (GA D S × GA D T) (mM θ S T) (mM_unitary hθ)`. Establish `sm` using `sm_of_theta (S := S) (T := T) h hψ`. Establish `hfin : ∀ p {u : WO S T}, u.map (infPart D) = 0 → ∀ F, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F → Ω p (rhoB hψ u F) = rhoB hψ u (Ω p F)` using `fun p u hu F hF => hcomm p _ (rhoB_comm h hψ hu) F hF`.

Establish `hth : ∀ p F, IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (Ω p F).1`. Introduce `p F hF`. Take `⟨U, hU, hl⟩` from `hF.level`. Use `theta_of_sm h hψ _ (hsm p F (sm F hF)) ⟨U, hU, fun u hu h0 => ?_⟩` and prove the remaining obligations. Establish `e : rhoB hψ u F = F` using `QB_ext fun x => by rw [coe_rhoB, hl u hu h0]`.

Rewrite using `[← coe_rhoB hψ, ← hfin p h0 F (sm F hF), e]`. Take `⟨om, hom⟩` from `exists_hom hψ Ω hth (fun p F F' h1 h2 => hadd p F F' (sm F h1) (sm F' h2)) (fun p a F h1 => hsmul p a F (sm F h1)) (fun F h1 => hone F (sm F h1)) fun p p' F h1 => hmul p p' F (sm F h1)`. Establish `lift : ∀ f, IsThetaFunO ψ S T f → ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f` using `fun f hf => ⟨toB hψ f hf, coe_toB hψ f hf⟩`. Apply the tactic sequence `refine ⟨om, ⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_, fun g hg k hk w f hf => ?_, fun sS sT hS hT g _ k _ cS cT f hf hv => ?_⟩ <;> obtain ⟨F, rfl⟩ := lift f hf`. Rewrite using `[hom p F hf]`.

Conclude with `hth p F hf`. Simplify using `only [hom _ F hf]`. Conclude with `(ev _ _ w).continuous.comp (hcont (continuous_mM hθ) F (sm F hf))`. Rewrite using `[hom p F hf]`. Conclude with `lintegral_eq_of_norms hψ μ 𝓕 hμ h𝓕 fun H _ _ _ Φ hΦ => hunit H Φ (fun v => hΦ _) p F (sm F hf)`.

Rewrite using `[hom _ F hf, htriv _ (mM_fin hg hk) F (sm F hf)]`. Take `⟨u, v, hu, rfl⟩` from `exists_parts h w`. Establish `h1 : IsThetaFunO ψ S T (rhoV hψ σ S T v F).1`. Rewrite using `[coe_rhoV]`. Conclude with `theta_heisO_real hθ hψ (real_iotaV h v) hf`.

Establish `h2 : IsThetaFunO ψ S T (rhoB hψ u (rhoV hψ σ S T v F)).1`. Rewrite using `[coe_rhoB]`. Conclude with `GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 h1 hu`. Establish `e1 : actO S T g k (u + iotaV σ S T v) = u + iotaV σ S T (mM θ S T (g, k) *ᵥ v)`. Rewrite using `[GlobalTheory.WeilVacMove.actO_add, actO_fin h hg hk hu, actO_iotaV h]`.

Rewrite using `[hom _ F hf, e1, ← coe_rhoB hψ _ F, ← coe_rhoB hψ _ (Ω (g, k) F), rhoB_add h hψ hu v F, rhoB_add h hψ hu _ (Ω (g, k) F), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm F hf)]`. Establish `hc` using `HM_cartan hS hT`. Rewrite using `[hom _ F hf, hvac _ _ hc.1 hc.2 (blk_comm_mM cS cT) F (sm F hf) (fderiv_vac h hψ F (sm F hf) sS sT hv), detPlus_pairMatrix sS sT g k]`. Both sides reduce to the same expression.
-/
theorem exists_isInfWeil : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ S T : HSp D, ∃ om, GlobalTheory.WeilParts.IsInfWeil ψ θ S T om := by
  intro D ψ hψ θ hθ S T
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨Ω, ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩, htriv, hcont, hvac⟩ :=
    GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian (Ix S T) (HM S T) HM_herm HM_det (BB ψ S T) (rhoV hψ σ S T) (isHeis_rhoB h hψ) (GA D S × GA D T)
      (mM θ S T) (mM_unitary hθ)
  have sm := sm_of_theta (S := S) (T := T) h hψ
  have hfin : ∀ p {u : WO S T}, u.map (infPart D) = 0 → ∀ F, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F →
      Ω p (rhoB hψ u F) = rhoB hψ u (Ω p F) := fun p u hu F hF => hcomm p _ (rhoB_comm h hψ hu) F hF
  have hth : ∀ p F, IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (Ω p F).1 := by
    intro p F hF
    obtain ⟨U, hU, hl⟩ := hF.level
    refine theta_of_sm h hψ _ (hsm p F (sm F hF)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoB hψ u F = F := QB_ext fun x => by rw [coe_rhoB, hl u hu h0]
    rw [← coe_rhoB hψ, ← hfin p h0 F (sm F hF), e]
  obtain ⟨om, hom⟩ := exists_hom hψ Ω hth (fun p F F' h1 h2 => hadd p F F' (sm F h1) (sm F' h2))
    (fun p a F h1 => hsmul p a F (sm F h1)) (fun F h1 => hone F (sm F h1)) fun p p' F h1 => hmul p p' F (sm F h1)
  have lift : ∀ f, IsThetaFunO ψ S T f → ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    fun f hf => ⟨toB hψ f hf, coe_toB hψ f hf⟩
  refine ⟨om, ⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk w f hf => ?_, fun sS sT hS hT g _ k _ cS cT f hf hv => ?_⟩ <;> obtain ⟨F, rfl⟩ := lift f hf
  · rw [hom p F hf]
    exact hth p F hf
  · simp only [hom _ F hf]
    exact (ev _ _ w).continuous.comp (hcont (continuous_mM hθ) F (sm F hf))
  · rw [hom p F hf]
    exact lintegral_eq_of_norms hψ μ 𝓕 hμ h𝓕 fun H _ _ _ Φ hΦ => hunit H Φ (fun v => hΦ _) p F (sm F hf)
  · rw [hom _ F hf, htriv _ (mM_fin hg hk) F (sm F hf)]
  · obtain ⟨u, v, hu, rfl⟩ := exists_parts h w
    have h1 : IsThetaFunO ψ S T (rhoV hψ σ S T v F).1 := by
      rw [coe_rhoV]
      exact theta_heisO_real hθ hψ (real_iotaV h v) hf
    have h2 : IsThetaFunO ψ S T (rhoB hψ u (rhoV hψ σ S T v F)).1 := by
      rw [coe_rhoB]
      exact GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 h1 hu
    have e1 : actO S T g k (u + iotaV σ S T v) = u + iotaV σ S T (mM θ S T (g, k) *ᵥ v) := by
      rw [GlobalTheory.WeilVacMove.actO_add, actO_fin h hg hk hu, actO_iotaV h]
    rw [hom _ F hf, e1, ← coe_rhoB hψ _ F, ← coe_rhoB hψ _ (Ω (g, k) F), rhoB_add h hψ hu v F,
      rhoB_add h hψ hu _ (Ω (g, k) F), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm F hf)]
  · have hc := HM_cartan hS hT
    rw [hom _ F hf, hvac _ _ hc.1 hc.2 (blk_comm_mM cS cT) F (sm F hf) (fderiv_vac h hψ F (sm F hf) sS sT hv), detPlus_pairMatrix sS sT g k]
    rfl

end GlobalTheory.RealWeil

end
