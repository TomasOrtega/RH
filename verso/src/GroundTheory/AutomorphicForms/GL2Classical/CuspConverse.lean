import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Cuspidal

open NumberField IsDedekindDomain Matrix MeasureTheory Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global ModularForm

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

/- English proof (translation)
Use `UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2 ?_` and prove the remaining obligations. Establish `: ((↑) ∘ fun t : ℝ => t +ᵥ z) = fun t : ℝ => (t : ℂ) + (z : ℂ)`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp_apply, coe_vadd]`. Rewrite using `[this]`.

Use `fun_prop`.
-/
theorem continuous_vadd_upperHalfPlane (z : ℍ) : Continuous fun t : ℝ => t +ᵥ z := by
  refine UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2 ?_
  have : ((↑) ∘ fun t : ℝ => t +ᵥ z) = fun t : ℝ => (t : ℂ) + (z : ℂ) := by
    funext t
    simp only [Function.comp_apply, coe_vadd]
  rw [this]
  fun_prop

/- English proof (translation)
Introduce `w`. Distinguish the cases in `hw : 0 < w.im`. Establish `hw' : 0 < (w + M).im` using `by simpa using hw`. Simplify using `only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]`. Rewrite using `[← hper ⟨w, hw⟩]`.

Use `congr 1`. Use `ext`. Simplify using `[coe_vadd, add_comm]`. Use `push Not at hw`. Establish `hw' : (w + M).im ≤ 0` using `by simpa using hw`.

Simplify using `[ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]`.
-/
theorem periodic_comp_ofComplex_of_vadd {F : ℍ → ℂ} {M : ℝ} (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) :
    Function.Periodic (F ∘ ofComplex) M := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + M).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]
  · push Not at hw
    have hw' : (w + M).im ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

/- English proof (translation)
Establish `hfper` using `periodic_comp_ofComplex_of_vadd hper`. Establish `han` using `analyticAt_cuspFunction_zero hM hfper hhol hbdd`. Establish `e : (cuspFunction M F ∘ fun τ : ℍ => Function.Periodic.qParam M τ) = F`. Use function extensionality and compare the values at `τ`. Simplify using `using eq_cuspFunction τ hM.ne' hfper`.

Simplify `han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hM)` using `[e]`.
-/
theorem tendsto_atImInfty_of_periodic_of_mdifferentiable {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F) :
    Tendsto F atImInfty (𝓝 (cuspFunction M F 0)) := by
  have hfper := periodic_comp_ofComplex_of_vadd hper
  have han := analyticAt_cuspFunction_zero hM hfper hhol hbdd
  have e : (cuspFunction M F ∘ fun τ : ℍ => Function.Periodic.qParam M τ) = F := by
    funext τ
    simpa using eq_cuspFunction τ hM.ne' hfper
  simpa [e] using han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hM)

/- English proof (translation)
Use `set c := cuspFunction M F 0`. Establish `ht` using `tendsto_atImInfty_of_periodic_of_mdifferentiable hM hper hhol hbdd`. It suffices to establish `hc : c = 0 by`. Rewrite using `[IsZeroAtImInfty, ZeroAtFilter, ← hc]`. Conclude with `ht`.

Use `norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)` and prove the remaining obligations. Rewrite using `[zero_add]`. Take `⟨A, hA⟩` from `(atImInfty_mem _).1 (ht.eventually (Metric.closedBall_mem_nhds c hε))`. Establish `hY : 0 < max A 1` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Use `set z₀ : ℍ := ⟨(max A 1 : ℝ) * Complex.I, by simp [hY]⟩`.

Establish `hbound : ∀ t : ℝ, ‖F (t +ᵥ z₀) - c‖ ≤ ε`. Introduce `t`. Establish `hz : A ≤ (t +ᵥ z₀).im`. Rewrite using `[vadd_im]`. Use `show A ≤ ((max A 1 : ℝ) * Complex.I).im`.

Simplify using the standard rewrite rules. Use `hA _ hz` as an intermediate fact. Simplify `this` using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `hcont : Continuous fun t : ℝ => F (t +ᵥ z₀)` using `hhol.continuous.comp (continuous_vadd_upperHalfPlane z₀)`. Establish `hint' : ∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c) = -(M • c)`.

Rewrite using `[intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const, hint z₀, intervalIntegral.integral_const, sub_zero, zero_sub]`. Establish `hle : ‖∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c)‖ ≤ ε * |M - 0|` using `intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hbound t`. Rewrite `hle` using `[hint', norm_neg, norm_smul, Real.norm_eq_abs, sub_zero, abs_of_pos hM]`. Conclude with `le_of_mul_le_mul_left (by linarith [hle] : M * ‖c‖ ≤ M * ε) hM`.
-/
theorem isZeroAtImInfty_of_integral_vadd_eq_zero {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F)
    (hint : ∀ z : ℍ, ∫ t in (0 : ℝ)..M, F (t +ᵥ z) = 0) : IsZeroAtImInfty F := by
  set c := cuspFunction M F 0
  have ht := tendsto_atImInfty_of_periodic_of_mdifferentiable hM hper hhol hbdd
  suffices hc : c = 0 by
    rw [IsZeroAtImInfty, ZeroAtFilter, ← hc]
    exact ht
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 (ht.eventually (Metric.closedBall_mem_nhds c hε))
  have hY : 0 < max A 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set z₀ : ℍ := ⟨(max A 1 : ℝ) * Complex.I, by simp [hY]⟩
  have hbound : ∀ t : ℝ, ‖F (t +ᵥ z₀) - c‖ ≤ ε := by
    intro t
    have hz : A ≤ (t +ᵥ z₀).im := by
      rw [vadd_im]
      show A ≤ ((max A 1 : ℝ) * Complex.I).im
      simp
    have := hA _ hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hcont : Continuous fun t : ℝ => F (t +ᵥ z₀) :=
    hhol.continuous.comp (continuous_vadd_upperHalfPlane z₀)
  have hint' : ∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c) = -(M • c) := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const, hint z₀,
      intervalIntegral.integral_const, sub_zero, zero_sub]
  have hle : ‖∫ t in (0 : ℝ)..M, (F (t +ᵥ z₀) - c)‖ ≤ ε * |M - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hbound t
  rw [hint', norm_neg, norm_smul, Real.norm_eq_abs, sub_zero, abs_of_pos hM] at hle
  exact le_of_mul_le_mul_left (by linarith [hle] : M * ‖c‖ ≤ M * ε) hM

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h z => integral_vadd_eq_zero hhol hM hper h z, isZeroAtImInfty_of_integral_vadd_eq_zero hM hper hhol hbdd⟩`.
-/
theorem isZeroAtImInfty_iff_integral_vadd_eq_zero {F : ℍ → ℂ} {M : ℝ} (hM : 0 < M)
    (hper : ∀ z : ℍ, F (M +ᵥ z) = F z) (hhol : MDiff F) (hbdd : IsBoundedAtImInfty F) :
    IsZeroAtImInfty F ↔ ∀ z : ℍ, ∫ t in (0 : ℝ)..M, F (t +ᵥ z) = 0 :=
  ⟨fun h z => integral_vadd_eq_zero hhol hM hper h z,
    isZeroAtImInfty_of_integral_vadd_eq_zero hM hper hhol hbdd⟩

variable {N : ℕ} [NeZero N] {k : ℤ}

/- English proof (translation)
Establish `hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f` using `fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ`. Use `set φ : AdelicGL ℚ 2 → ℂ := ↑(liftEquiv N k f)`. Establish `hφ : IsWeightLevel N k φ` using `(liftEquiv N k f).2`. Use `set w := finiteDiagonal ℚ 2 δ⁻¹`. Take `⟨M, hM, hconj⟩` from `exists_level_conj N w`.

Establish `: NeZero M` using `⟨hM.ne'⟩`. Establish `hw : w = finiteDiagonal ℚ 2 δ⁻¹ * 1` using `(mul_one _).symm`. Establish `hMmem : algebraMap ℚ 𝔸f (M : ℚ) ∈ levelIdeal M` using `⟨1, one_mem _, by simp⟩`. Establish `hmem : finiteDiagonal ℚ 2 (δ * unipRat M * δ⁻¹) ∈ Gamma0Level N`. Use `finiteDiagonal_conj_mem hconj (one_mem _) hw hMmem` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Use `set F := (f : ℍ → ℂ) ∣[k] toReal δ`. Establish `hper : ∀ z : ℍ, F ((M : ℝ) +ᵥ z) = F z`. Introduce `z`. Use `slash_periodic hf (M : ℚ) hmem z` as an intermediate fact.

Simplify using `using this`. Use `⟨M, hM, hper, fun z => ?_⟩` and prove the remaining obligations. Use `set h := borelGL z`. Establish `hpos : 0 < h.det.val` using `det_borelGL_pos z`. Establish `hδR : 0 < (toReal δ).det.val` using `by rw [det_toReal]; exact_mod_cast hδ`.

Establish `hdne : ((toReal δ).det.val : ℂ) ^ (k - 1) ≠ 0` using `zpow_ne_zero _ (by exact_mod_cast hδR.ne')`. Use `set j := denom h ((UpperHalfPlane.I : ℍ) : ℂ)`. Use `set C : ℂ := (((toReal δ).det.val : ℂ) ^ (k - 1))⁻¹ * (Real.sqrt (toReal δ).det.val : ℂ) ^ k * ((j / (‖j‖ : ℂ)) ^ (-k) * (Real.sqrt (h • UpperHalfPlane.I).im : ℂ) ^ k)`. Establish `hj : j = 1` using `denom_borelGL z _`. Establish `hhI : h • UpperHalfPlane.I = z` using `borelGL_smul_I z`.

Establish `hC : C ≠ 0`. Establish `h1 : (Real.sqrt (toReal δ).det.val : ℂ) ≠ 0`. Conclude with `(Real.sqrt_pos.2 hδR).ne'` after adjusting the coercions. Establish `h2 : (Real.sqrt (h • UpperHalfPlane.I).im : ℂ) ≠ 0`. Conclude with `(Real.sqrt_pos.2 (h • UpperHalfPlane.I).im_pos).ne'` after adjusting the coercions.

Simplify using `only [C, hj, norm_one, Complex.ofReal_one, div_one, _root_.one_zpow, one_mul]`. Conclude with `mul_ne_zero (mul_ne_zero (inv_ne_zero hdne) (zpow_ne_zero _ h1)) (zpow_ne_zero _ h2)`. Establish `key : ∀ t : ℝ, archLift k f (toReal δ * (unipReal t * h)) = C * F (t +ᵥ z)`. Introduce `t`. Establish `hy : 0 < (unipReal t * h).det.val`.

Rewrite using `[map_mul, Units.val_mul, det_unipReal, one_mul]`. Conclude with `hpos`. Establish `h1` using `archLift_mul_left (k := k) (f : ℍ → ℂ) hδR hy`. Rewrite `h1` using `[archLift_unipReal_mul F hpos t]`. Rewrite using `[eq_inv_mul_iff_mul_eq₀ hdne |>.2 h1, ← hhI]`.

Simplify using `only [C, j]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : ∀ t : ℝ, φ (realEmb (unipReal t * h) * finEmb ℚ 2 w) = C * F (t +ᵥ z)`. Introduce `t`. Rewrite using `[hw, hφ.apply_realEmb_mul_finiteDiagonal δ⁻¹ _ (one_mem _), map_inv, inv_inv, ← key t]`.

Use `adelicLift_realEmb hf ?_` and prove the remaining obligations. Rewrite using `[map_mul, Units.val_mul]`. Use `mul_pos hδR ?_` and prove the remaining obligations. Rewrite using `[map_mul, Units.val_mul, det_unipReal, one_mul]`. Conclude with `hpos`.

Use `⟨levelConstant M * C, mul_ne_zero (by exact_mod_cast (levelConstant_pos M).ne') hC, ?_⟩` and prove the remaining obligations. Rewrite using `[constantTerm_realEmb_mul_finEmb_of_conj hφ h hconj]`. Repeatedly rewrite using `[hint]`. Rewrite using `[intervalIntegral.integral_const_mul, Complex.real_smul]`. Simplify using `only [C]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem constantTerm_liftEquiv_finiteDiagonal_inv
    (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (δ : GL (Fin 2) ℚ)
    (hδ : 0 < (δ.det.val : ℚ)) :
    ∃ M : ℕ, 0 < M ∧ (∀ z : ℍ, ((f : ℍ → ℂ) ∣[k] toReal δ) ((M : ℝ) +ᵥ z) = ((f : ℍ → ℂ) ∣[k] toReal δ) z) ∧
      ∀ z : ℍ, ∃ c : ℂ, c ≠ 0 ∧
        constantTerm 1 (liftEquiv N k f : AdelicGL ℚ 2 → ℂ)
            (realEmb (borelGL z) * finEmb ℚ 2 (finiteDiagonal ℚ 2 δ⁻¹)) =
          c * ∫ t in (0 : ℝ)..M, ((f : ℍ → ℂ) ∣[k] toReal δ) (t +ᵥ z) := by
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f := fun γ hγ =>
    SlashInvariantForm.slash_action_eqn f γ hγ
  set φ : AdelicGL ℚ 2 → ℂ := ↑(liftEquiv N k f)
  have hφ : IsWeightLevel N k φ := (liftEquiv N k f).2
  set w := finiteDiagonal ℚ 2 δ⁻¹
  obtain ⟨M, hM, hconj⟩ := exists_level_conj N w
  have : NeZero M := ⟨hM.ne'⟩
  have hw : w = finiteDiagonal ℚ 2 δ⁻¹ * 1 := (mul_one _).symm
  have hMmem : algebraMap ℚ 𝔸f (M : ℚ) ∈ levelIdeal M := ⟨1, one_mem _, by simp⟩
  have hmem : finiteDiagonal ℚ 2 (δ * unipRat M * δ⁻¹) ∈ Gamma0Level N := by
    have := finiteDiagonal_conj_mem hconj (one_mem _) hw hMmem
    rwa [inv_inv] at this
  set F := (f : ℍ → ℂ) ∣[k] toReal δ
  have hper : ∀ z : ℍ, F ((M : ℝ) +ᵥ z) = F z := by
    intro z
    have := slash_periodic hf (M : ℚ) hmem z
    simpa using this
  refine ⟨M, hM, hper, fun z => ?_⟩
  set h := borelGL z
  have hpos : 0 < h.det.val := det_borelGL_pos z
  have hδR : 0 < (toReal δ).det.val := by rw [det_toReal]; exact_mod_cast hδ
  have hdne : ((toReal δ).det.val : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hδR.ne')
  set j := denom h ((UpperHalfPlane.I : ℍ) : ℂ)
  set C : ℂ := (((toReal δ).det.val : ℂ) ^ (k - 1))⁻¹ * (Real.sqrt (toReal δ).det.val : ℂ) ^ k *
    ((j / (‖j‖ : ℂ)) ^ (-k) * (Real.sqrt (h • UpperHalfPlane.I).im : ℂ) ^ k)
  have hj : j = 1 := denom_borelGL z _
  have hhI : h • UpperHalfPlane.I = z := borelGL_smul_I z
  have hC : C ≠ 0 := by
    have h1 : (Real.sqrt (toReal δ).det.val : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hδR).ne'
    have h2 : (Real.sqrt (h • UpperHalfPlane.I).im : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (h • UpperHalfPlane.I).im_pos).ne'
    simp only [C, hj, norm_one, Complex.ofReal_one, div_one, _root_.one_zpow, one_mul]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hdne) (zpow_ne_zero _ h1)) (zpow_ne_zero _ h2)
  have key : ∀ t : ℝ, archLift k f (toReal δ * (unipReal t * h)) = C * F (t +ᵥ z) := by
    intro t
    have hy : 0 < (unipReal t * h).det.val := by
      rw [map_mul, Units.val_mul, det_unipReal, one_mul]
      exact hpos
    have h1 := archLift_mul_left (k := k) (f : ℍ → ℂ) hδR hy
    rw [archLift_unipReal_mul F hpos t] at h1
    rw [eq_inv_mul_iff_mul_eq₀ hdne |>.2 h1, ← hhI]
    simp only [C, j]
    ring
  have hint : ∀ t : ℝ, φ (realEmb (unipReal t * h) * finEmb ℚ 2 w) = C * F (t +ᵥ z) := by
    intro t
    rw [hw, hφ.apply_realEmb_mul_finiteDiagonal δ⁻¹ _ (one_mem _), map_inv, inv_inv, ← key t]
    refine adelicLift_realEmb hf ?_
    rw [map_mul, Units.val_mul]
    refine mul_pos hδR ?_
    rw [map_mul, Units.val_mul, det_unipReal, one_mul]
    exact hpos
  refine ⟨levelConstant M * C, mul_ne_zero (by exact_mod_cast (levelConstant_pos M).ne') hC, ?_⟩
  rw [constantTerm_realEmb_mul_finEmb_of_conj hφ h hconj]
  simp_rw [hint]
  rw [intervalIntegral.integral_const_mul, Complex.real_smul]
  simp only [C]
  ring

/- English proof (translation)
Establish `hc : IsCusp (toReal δ • (OnePoint.infty : OnePoint ℝ)) (Gamma0 N : Subgroup (GL (Fin 2) ℝ))`. Rewrite using `[Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]`. Use `⟨δ • OnePoint.infty, ?_⟩` and prove the remaining obligations. Rewrite using `[← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty]`. Both sides reduce to the same expression.

Conclude with `f.bdd_at_cusps' hc (toReal δ) rfl`.
-/
theorem isBoundedAtImInfty_slash_toReal (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : GL (Fin 2) ℚ) : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] toReal δ) := by
  have hc : IsCusp (toReal δ • (OnePoint.infty : OnePoint ℝ)) (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    refine ⟨δ • OnePoint.infty, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty]
    rfl
  exact f.bdd_at_cusps' hc (toReal δ) rfl

/- English proof (translation)
Take `⟨M, hM, hper, hct⟩` from `constantTerm_liftEquiv_finiteDiagonal_inv f.toSlashInvariantForm δ hδ`. Use `isZeroAtImInfty_of_integral_vadd_eq_zero (M := M) (by exact_mod_cast hM) hper (f.holo'.slash k (toReal δ)) (isBoundedAtImInfty_slash_toReal f δ) fun z => ?_` and prove the remaining obligations. Take `⟨c, hc, he⟩` from `hct z`. Establish `h0` using `hcusp 1 one_pos (by norm_num) (realEmb (borelGL z) * finEmb ℚ 2 (finiteDiagonal ℚ 2 δ⁻¹))`. Rewrite `h0` using `[he]`.

Conclude with `(mul_eq_zero.1 h0).resolve_left hc`.
-/
theorem isZeroAtImInfty_slash_of_isCuspidal (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hcusp : IsCuspidal (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ)) (δ : GL (Fin 2) ℚ)
    (hδ : 0 < (δ.det.val : ℚ)) : IsZeroAtImInfty ((f : ℍ → ℂ) ∣[k] toReal δ) := by
  obtain ⟨M, hM, hper, hct⟩ := constantTerm_liftEquiv_finiteDiagonal_inv f.toSlashInvariantForm δ hδ
  refine isZeroAtImInfty_of_integral_vadd_eq_zero (M := M) (by exact_mod_cast hM) hper
    (f.holo'.slash k (toReal δ)) (isBoundedAtImInfty_slash_toReal f δ) fun z => ?_
  obtain ⟨c, hc, he⟩ := hct z
  have h0 := hcusp 1 one_pos (by norm_num) (realEmb (borelGL z) * finEmb ℚ 2 (finiteDiagonal ℚ 2 δ⁻¹))
  rw [he] at h0
  exact (mul_eq_zero.1 h0).resolve_left hc

/- English proof (translation)
Rewrite using `[isCuspForm_iff]`. Introduce `c hc`. Rewrite `hc` using `[Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']`. Take `⟨σ, rfl⟩` from `hc`. Rewrite using `[OnePoint.isZeroAt_iff rfl, ← toReal_mapGL]`.

Use `isZeroAtImInfty_slash_of_isCuspidal f hcusp _ ?_` and prove the remaining obligations. Establish `h1` using `det_toReal (Matrix.SpecialLinearGroup.mapGL ℚ σ)`. Establish `h2 : (toReal (Matrix.SpecialLinearGroup.mapGL ℚ σ)).det.val = 1`. Rewrite using `[toReal_mapGL]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[h2]`. Establish `h3 : ((Matrix.SpecialLinearGroup.mapGL ℚ σ).det.val : ℚ) = 1` using `by exact_mod_cast h1.symm`. Rewrite using `[h3]`. Conclude with `one_pos`.
-/
theorem isCuspForm_of_isCuspidal_liftEquiv (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hcusp : IsCuspidal (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ)) : IsCuspForm f := by
  rw [isCuspForm_iff]
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
  obtain ⟨σ, rfl⟩ := hc
  rw [OnePoint.isZeroAt_iff rfl, ← toReal_mapGL]
  refine isZeroAtImInfty_slash_of_isCuspidal f hcusp _ ?_
  have h1 := det_toReal (Matrix.SpecialLinearGroup.mapGL ℚ σ)
  have h2 : (toReal (Matrix.SpecialLinearGroup.mapGL ℚ σ)).det.val = 1 := by
    rw [toReal_mapGL]
    simp
  rw [h2] at h1
  have h3 : ((Matrix.SpecialLinearGroup.mapGL ℚ σ).det.val : ℚ) = 1 := by exact_mod_cast h1.symm
  rw [h3]
  exact one_pos

/- English proof (translation)
Take `⟨F, hF⟩` from `isCuspForm_of_isCuspidal_liftEquiv f hcusp`. Conclude with `⟨F, congrArg (fun g : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k => (g : ℍ → ℂ)) hF⟩`.
-/
theorem exists_cuspForm_of_isCuspidal_liftEquiv (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hcusp : IsCuspidal (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ)) :
    ∃ F : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k, (F : ℍ → ℂ) = f := by
  obtain ⟨F, hF⟩ := isCuspForm_of_isCuspidal_liftEquiv f hcusp
  exact ⟨F, congrArg (fun g : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k => (g : ℍ → ℂ)) hF⟩

/- English proof (translation)
Use `⟨isCuspForm_of_isCuspidal_liftEquiv f, fun ⟨F, hF⟩ => ?_⟩` and prove the remaining obligations. Establish `e : f.toSlashInvariantForm = F.toSlashInvariantForm`. Substitute `hF` using the available equality. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `isCuspidal_liftEquiv_cuspForm F`.
-/
theorem isCuspidal_liftEquiv_iff_isCuspForm (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    IsCuspidal (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ↔ IsCuspForm f := by
  refine ⟨isCuspForm_of_isCuspidal_liftEquiv f, fun ⟨F, hF⟩ => ?_⟩
  have e : f.toSlashInvariantForm = F.toSlashInvariantForm := by
    subst hF
    rfl
  rw [e]
  exact isCuspidal_liftEquiv_cuspForm F

end GL2Classical

end

end GroundTheory.Automorphic
