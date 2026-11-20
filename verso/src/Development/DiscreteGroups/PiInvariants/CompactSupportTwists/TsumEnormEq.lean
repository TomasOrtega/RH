import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvA

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

set_option linter.unusedSimpArgs false

namespace DiscreteGroups.T1.G

variable (X : Ctx)

/- English proof (translation)
Establish `hfin` using `(hb X φ hφ).1 x y`. Use `set s := hfin.toFinset`. Establish `hs : (Function.support fun γ : X.Γ => ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ) ⊆ s`. Introduce `γ hγ`. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]`.

Simplify using `using hγ`. Establish `hs' : (Function.support fun γ : X.Γ => ((‖φ (x⁻¹ * (γ : X.G) * y)‖ : ℝ) : ℂ)) ⊆ s`. Introduce `γ hγ`. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]`. Simplify using `using hγ`.

Rewrite using `[tsum_eq_sum' hs]`. Unfold `ker`. Rewrite using `[finsum_eq_sum_of_support_subset _ hs', ← Complex.ofReal_sum, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _), ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]`. Simplify using `[ofReal_norm]`.
-/
theorem tsum_enorm_eq (hb : KerBasic) {φ : X.G → ℂ} (hφ : Tst φ) (x y : X.G) :
    ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ = ‖ker X.Γ (fun w => ((‖φ w‖ : ℝ) : ℂ)) x y‖ₑ := by
  have hfin := (hb X φ hφ).1 x y
  set s := hfin.toFinset
  have hs : (Function.support fun γ : X.Γ => ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ) ⊆ s := by
    intro γ hγ
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    simpa using hγ
  have hs' : (Function.support fun γ : X.Γ => ((‖φ (x⁻¹ * (γ : X.G) * y)‖ : ℝ) : ℂ)) ⊆ s := by
    intro γ hγ
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    simpa using hγ
  rw [tsum_eq_sum' hs]
  unfold ker
  rw [finsum_eq_sum_of_support_subset _ hs', ← Complex.ofReal_sum, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
    ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
  simp [ofReal_norm]

/- English proof (translation)
Rewrite using `[← lintegral_tsum]`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Simplify using `only [enorm_mul]`. Rewrite using `[ENNReal.tsum_mul_right, tsum_enorm_eq X hb hφ x y]`. Introduce `γ`.

Conclude with `((hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hf).enorm`.
-/
theorem lint_unfold (hb : KerBasic) {φ : X.G → ℂ} (hφ : Tst φ) {f : X.G → ℂ}
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : AEStronglyMeasurable f X.ν) (x : X.G) :
    ∑' γ : X.Γ, ∫⁻ y, ‖φ (x⁻¹ * (γ : X.G) * y) * f y‖ₑ ∂X.ν =
      ∫⁻ y, ‖ker X.Γ (fun w => ((‖φ w‖ : ℝ) : ℂ)) x y * f y‖ₑ ∂X.ν := by
  rw [← lintegral_tsum]
  · refine lintegral_congr fun y => ?_
    simp only [enorm_mul]
    rw [ENNReal.tsum_mul_right, tsum_enorm_eq X hb hφ x y]
  · intro γ
    exact ((hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hf).enorm

/- English proof (translation)
Establish `hfm : AEStronglyMeasurable f X.μ` using `aesm_of_inv X hinv hf.1`. Establish `hk` using `(hl2 X _ (tst_norm X hφ)).2 x`. Establish `hint : Integrable (fun y => ker X.Γ (fun w => ((‖φ w‖ : ℝ) : ℂ)) x y * f y) X.ν` using `hk.integrable_mul hf`. Establish `hlu` using `lint_unfold X hb hφ hinv hf.1 x`. Establish `hgm : AEStronglyMeasurable (fun y => φ (x⁻¹ * y) * f y) X.μ` using `(hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hfm`.

Establish `hlin : ∫⁻ y, ‖φ (x⁻¹ * y) * f y‖ₑ ∂X.μ = ∑' γ : X.Γ, ∫⁻ y, ‖φ (x⁻¹ * (γ : X.G) * y) * f y‖ₑ ∂X.ν`. Rewrite using `[X.fd.lintegral_eq_tsum'']`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Simplify using `only [Subgroup.smul_def, smul_eq_mul]`.

Rewrite using `[hinv γ y, mul_assoc]`. Establish `hgi : Integrable (fun y => φ (x⁻¹ * y) * f y) X.μ` using `⟨hgm, by rw [HasFiniteIntegral, hlin, hlu]; exact hint.2⟩`. Use `⟨hgi, ?_⟩` and prove the remaining obligations. Rewrite using `[X.fd.integral_eq_tsum'' _ hgi]`. Establish `h1 : ∀ γ : X.Γ, ∫ y in X.F, φ (x⁻¹ * ((γ : X.Γ) • y)) * f ((γ : X.Γ) • y) ∂X.μ = ∫ y, φ (x⁻¹ * (γ : X.G) * y) * f y ∂X.ν` using `fun γ => by show _ = ∫ y in X.F, _ ∂X.μ`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [Subgroup.smul_def, smul_eq_mul]`. Rewrite using `[hinv γ y, mul_assoc]`. Repeatedly rewrite using `[h1]`. Rewrite using `[← integral_tsum]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[tsum_mul_right, tsum_eq_finsum ((hb X φ hφ).1 x y)]`. Both sides reduce to the same expression. Introduce `γ`.

Conclude with `(hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hf.1`. Rewrite using `[lint_unfold X hb hφ hinv hf.1 x]`. Conclude with `hint.2.ne`.
-/
theorem unfold (hb : KerBasic) (hl2 : KernelL2RowsColumns) {φ : X.G → ℂ} (hφ : Tst φ) {f : X.G → ℂ}
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (x : X.G) :
    Integrable (fun y => φ (x⁻¹ * y) * f y) X.μ ∧
    ∫ y, ker X.Γ φ x y * f y ∂X.ν = ∫ y, φ (x⁻¹ * y) * f y ∂X.μ := by
  have hfm : AEStronglyMeasurable f X.μ := aesm_of_inv X hinv hf.1
  have hk := (hl2 X _ (tst_norm X hφ)).2 x
  have hint : Integrable (fun y => ker X.Γ (fun w => ((‖φ w‖ : ℝ) : ℂ)) x y * f y) X.ν := hk.integrable_mul hf
  have hlu := lint_unfold X hb hφ hinv hf.1 x
  have hgm : AEStronglyMeasurable (fun y => φ (x⁻¹ * y) * f y) X.μ :=
    (hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hfm
  have hlin : ∫⁻ y, ‖φ (x⁻¹ * y) * f y‖ₑ ∂X.μ =
      ∑' γ : X.Γ, ∫⁻ y, ‖φ (x⁻¹ * (γ : X.G) * y) * f y‖ₑ ∂X.ν := by
    rw [X.fd.lintegral_eq_tsum'']
    refine tsum_congr fun γ => ?_
    refine lintegral_congr fun y => ?_
    simp only [Subgroup.smul_def, smul_eq_mul]
    rw [hinv γ y, mul_assoc]
  have hgi : Integrable (fun y => φ (x⁻¹ * y) * f y) X.μ :=
    ⟨hgm, by rw [HasFiniteIntegral, hlin, hlu]; exact hint.2⟩
  refine ⟨hgi, ?_⟩
  rw [X.fd.integral_eq_tsum'' _ hgi]
  have h1 : ∀ γ : X.Γ, ∫ y in X.F, φ (x⁻¹ * ((γ : X.Γ) • y)) * f ((γ : X.Γ) • y) ∂X.μ =
      ∫ y, φ (x⁻¹ * (γ : X.G) * y) * f y ∂X.ν := fun γ => by
    show _ = ∫ y in X.F, _ ∂X.μ
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Subgroup.smul_def, smul_eq_mul]
    rw [hinv γ y, mul_assoc]
  simp_rw [h1]
  rw [← integral_tsum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [tsum_mul_right, tsum_eq_finsum ((hb X φ hφ).1 x y)]
    rfl
  · intro γ
    exact (hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hf.1
  · rw [lint_unfold X hb hφ hinv hf.1 x]
    exact hint.2.ne

end DiscreteGroups.T1.G

end
