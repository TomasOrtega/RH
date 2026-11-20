import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralArchimedeanMatricesLeftMulJacobianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf.SecAffine

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Unfold `htInf`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_inv, htGL_inv]`.
-/
theorem htInf_inv_eq (g : GL (Fin n) (Cinf E)) : htInf g⁻¹ = htInf g := by
  unfold htInf
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_inv, htGL_inv]

end GlobalTheory.JSW.MirCinf.SecAffine

namespace GlobalTheory.JSW.MirCinf

/- English proof (translation)
Introduce `E _ _ n Z _ _ _ σ₀ L χ α hχ hσ hα hαu X _ ν _ κ τ hκ hτ hmom hk`. Choose the witnesses or unpack the hypotheses as in `⟨R1, hR1⟩ : ∃ R1 : ℝ, ∀ z ∈ tsupport χ, htInf (toGLInf (Matrix.of (σ₀ + L z))) ≤ R1 := by`. Establish `hc : ContinuousOn (fun z => htInf (toGLInf (Matrix.of (σ₀ + L z)))) (tsupport χ)` using `SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.comp (by fun_prop : Continuous fun z => σ₀ + L z).continuousOn fun z hz => hσ z hz)`. Take `⟨C, hC⟩` from `hχ.isCompact.exists_bound_of_continuousOn hc`. Conclude with `⟨C, fun z hz => (Real.le_norm_self _).trans (hC z hz)⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨R2, hR2⟩ : ∃ R2 : ℝ, ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R2 := by`. Establish `hc : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α)` using `SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.mono hαu)`. Take `⟨C, hC⟩` from `hα.isCompact.exists_bound_of_continuousOn hc`. Conclude with `⟨C, fun a ha => (Real.le_norm_self _).trans (hC a ha)⟩`. Use `⟨R1 * R2, ?_⟩` and prove the remaining obligations.

Introduce `W hW q z g`. Establish `hfam` using `GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ hκ hτ hmom (R1 * R2) σ₀ L`. Establish `hrap : IsRapidFInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf (R1 * R2) σ₀ κ τ q) (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ q)`. Take `⟨h1, h2, h3⟩` from `hfam`. Take `⟨m1, m2⟩` from `h2 Unit (fun _ => q) (fun _ _ => measurable_const)`.

Use `⟨m1.comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), h1, fun z => (m2 z).comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), fun N => ?_⟩` and prove the remaining obligations. Take `⟨C, M, hC⟩` from `h3 N`. Conclude with `(hC q).1`. Establish `hint : Integrable (fun p : (Fin n → Fin n → Cinf E) × X => secKInf (R1 * R2) σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν)` using `hrap.integrable hW z g`. Establish `hinner : ∀ h : Fin n → Fin n → Cinf E, ∫ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) * W (g * toGLInf (Matrix.of (h, x).1)) ∂ν = (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : …`.

Introduce `h`. Rewrite using `[hk z]`. Distinguish the cases in `hc : IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q`. Establish `hsum : ((0 : Z), sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) σ₀) + (z, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) (L z)) = (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin …`. Rewrite using `[Prod.mk_add_mk, zero_add]`.

Use `congr 1`. Use function extensionality and compare the values at `i j`. Simplify using `only [Pi.add_apply, sandCLMInf_apply]`. Rewrite using `[← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add]`. Both sides reduce to the same expression.

Establish `e : ∀ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) * W (g * toGLInf (Matrix.of (h, x).1)) = (((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * W (g * toGLInf (Matrix.of h))) * (κ x * (𝐞 (τ x (z, fun i j => (((q⁻¹ : G …`. Introduce `x`. Simplify using `only [secKInf, secEtaInf, if_pos hc]`. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, ← hsum, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, if_pos hc]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[secKInf, if_neg hc]`. Establish `hR : ∫ p, secKInf (R1 * R2) σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) = ∫ h : Fin n → Fin n → Cinf E, (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then ((jacIn …`. Rewrite using `[integral_prod _ hint]`.

Conclude with `integral_congr_ae (Filter.Eventually.of_forall hinner)`. Rewrite using `[hR]`. Distinguish the cases in `hz : χ z = 0`. Simplify using `[hz]`. Establish `hzK : z ∈ tsupport χ` using `subset_tsupport _ hz`.

Establish `hu` using `hσ z hzK`. Use `set σ' := toGLInf (Matrix.of (σ₀ + L z)) with hσ'`. Establish `hσv : (σ' : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of (σ₀ + L z)` using `val_toGLInf hu`. Rewrite using `[smoothMatInf, GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian E n (q⁻¹ * σ'), ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)` and prove the remaining obligations.

Simplify using `only`. Establish `hAh : Matrix.of (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) = ((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h` using `rfl`. Establish `ha : (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) = (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)`. Rewrite using `[Units.val_mul, hσv]`. Rewrite using `[hAh, ha]`.

Distinguish the cases in `hαz : α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) = 0`. Rewrite using `[hαz]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem` using `subset_tsupport _ hαz`. Establish `hAu : IsUnit (Matrix.of (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j))` using `hαu hmem`.

Rewrite `hAu`, `hmem` using `[← ha]`. Rewrite `hAu` using `[hAh]`. Establish `hh : IsUnit (Matrix.of h)` using `(Units.isUnit_units_mul _ _).1 hAu`. Establish `ht : toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (q⁻¹ * σ') * toGLInf (Matrix.of h)` using `Units.ext (by rw [val_toGLInf hAu, Units.val_mul (q⁻¹ * σ'), val_toGLInf hh])`. Establish `hb1` using `hR1 z hzK`.

Establish `hb2 : htInf (toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h)) ≤ R2` using `hR2 _ hmem`. Rewrite `hb2` using `[ht]`. Establish `hb1' : htInf σ' ≤ R1` using `hb1`. Establish `hbound : htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q`. Establish `e1 : toGLInf (Matrix.of h) = (q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h))` using `by group`.

Establish `p1` using `htInf_pos' σ'`. Establish `p2` using `htInf_pos' (q⁻¹ * σ' * toGLInf (Matrix.of h))`. Establish `p3` using `htInf_pos' q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[if_pos ⟨hh, hbound⟩]`.

Establish `hG : ((g * σ'⁻¹ * q : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h`. Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul]`. Use `congr 2`. Use `group`. Establish `hgt : toGLInf ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = g * toGLInf (Matrix.of h)` using `Units.ext (by rw [val_toGLInf (g.isUnit.mul hh), Units.val_mul, val_toGLInf hh])`.

Rewrite using `[hG, onMatInf_of_isUnit W (g.isUnit.mul hh), hgt, Units.val_mul, jacInf_mul, hσv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smoothMatInf_affine_eq_integral_secKInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  classical
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hσ hα hαu X _ ν _ κ τ hκ hτ hmom hk
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, ∀ z ∈ tsupport χ, htInf (toGLInf (Matrix.of (σ₀ + L z))) ≤ R1 := by
    have hc : ContinuousOn (fun z => htInf (toGLInf (Matrix.of (σ₀ + L z)))) (tsupport χ) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.comp
        (by fun_prop : Continuous fun z => σ₀ + L z).continuousOn fun z hz => hσ z hz)
    obtain ⟨C, hC⟩ := hχ.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun z hz => (Real.le_norm_self _).trans (hC z hz)⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R2 := by
    have hc : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.mono hαu)
    obtain ⟨C, hC⟩ := hα.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun a ha => (Real.le_norm_self _).trans (hC a ha)⟩
  refine ⟨R1 * R2, ?_⟩
  intro W hW q z g
  have hfam := GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ hκ hτ hmom (R1 * R2) σ₀ L
  have hrap : IsRapidFInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf (R1 * R2) σ₀ κ τ q)
      (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ q) := by
    obtain ⟨h1, h2, h3⟩ := hfam
    obtain ⟨m1, m2⟩ := h2 Unit (fun _ => q) (fun _ _ => measurable_const)
    refine ⟨m1.comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), h1,
      fun z => (m2 z).comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), fun N => ?_⟩
    obtain ⟨C, M, hC⟩ := h3 N
    exact (hC q).1
  have hint : Integrable (fun p : (Fin n → Fin n → Cinf E) × X => secKInf (R1 * R2) σ₀ κ τ q p *
      (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) :=
    hrap.integrable hW z g
  have hinner : ∀ h : Fin n → Fin n → Cinf E, ∫ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
      W (g * toGLInf (Matrix.of (h, x).1)) ∂ν =
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    intro h
    rw [hk z]
    by_cases hc : IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q
    · have hsum : ((0 : Z), sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) σ₀) +
          (z, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) (L z)) =
          (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
        rw [Prod.mk_add_mk, zero_add]
        congr 1
        funext i j
        simp only [Pi.add_apply, sandCLMInf_apply]
        rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add]
        rfl
      have e : ∀ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
          W (g * toGLInf (Matrix.of (h, x).1)) =
          (((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
            W (g * toGLInf (Matrix.of h))) *
          (κ x * (𝐞 (τ x (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
            Matrix.of (σ₀ + L z) * Matrix.of h) i j)) : ℂ)) := by
        intro x
        simp only [secKInf, secEtaInf, if_pos hc]
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, ← hsum, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, if_pos hc]
      ring
    · simp [secKInf, if_neg hc]
  have hR : ∫ p, secKInf (R1 * R2) σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))
      ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) = ∫ h : Fin n → Fin n → Cinf E,
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    rw [integral_prod _ hint]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [hR]
  by_cases hz : χ z = 0
  · simp [hz]
  have hzK : z ∈ tsupport χ := subset_tsupport _ hz
  have hu := hσ z hzK
  set σ' := toGLInf (Matrix.of (σ₀ + L z)) with hσ'
  have hσv : (σ' : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of (σ₀ + L z) := val_toGLInf hu
  rw [smoothMatInf, GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian E n (q⁻¹ * σ'), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  have hAh : Matrix.of (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      ((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := rfl
  have ha : (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
    rw [Units.val_mul, hσv]
  rw [hAh, ha]
  by_cases hαz : α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) = 0
  · rw [hαz]; ring
  have hmem := subset_tsupport _ hαz
  have hAu : IsUnit (Matrix.of (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) := hαu hmem
  rw [← ha] at hAu hmem
  rw [hAh] at hAu
  have hh : IsUnit (Matrix.of h) := (Units.isUnit_units_mul _ _).1 hAu
  have ht : toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (q⁻¹ * σ') * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf hAu, Units.val_mul (q⁻¹ * σ'), val_toGLInf hh])
  have hb1 := hR1 z hzK
  have hb2 : htInf (toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h)) ≤ R2 := hR2 _ hmem
  rw [ht] at hb2
  have hb1' : htInf σ' ≤ R1 := hb1
  have hbound : htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q := by
    have e1 : toGLInf (Matrix.of h) = (q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by group
    have p1 := htInf_pos' σ'
    have p2 := htInf_pos' (q⁻¹ * σ' * toGLInf (Matrix.of h))
    have p3 := htInf_pos' q
    calc htInf (toGLInf (Matrix.of h)) = htInf ((q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [← e1]
      _ ≤ htInf ((q⁻¹ * σ')⁻¹) * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := htInf_mul_le _ _
      _ = htInf (q⁻¹ * σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by rw [SecAffine.htInf_inv_eq]
      _ ≤ (htInf q⁻¹ * htInf σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) :=
          mul_le_mul_of_nonneg_right (htInf_mul_le _ _) p2.le
      _ = htInf q * (htInf σ' * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [SecAffine.htInf_inv_eq]; ring
      _ ≤ htInf q * (R1 * R2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hb1' hb2 p2.le (p1.le.trans hb1')) p3.le
      _ = R1 * R2 * htInf q := by ring
  rw [if_pos ⟨hh, hbound⟩]
  have hG : ((g * σ'⁻¹ * q : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
      (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := by
    rw [← Matrix.mul_assoc, ← Units.val_mul]
    congr 2
    group
  have hgt : toGLInf ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = g * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf (g.isUnit.mul hh), Units.val_mul, val_toGLInf hh])
  rw [hG, onMatInf_of_isUnit W (g.isUnit.mul hh), hgt, Units.val_mul, jacInf_mul, hσv]
  push_cast
  ring

end GlobalTheory.JSW.MirCinf
