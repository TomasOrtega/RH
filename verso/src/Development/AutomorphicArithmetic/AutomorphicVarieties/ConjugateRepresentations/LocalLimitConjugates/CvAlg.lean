import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvCount

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs`. Take `⟨hloc, hcnt⟩` from `locInt G Γ μ`. Take `⟨B, hB, hbd⟩` from `cvCount G Γ μ ψ hψ hψs`. Establish `hint : ∀ (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (x : G), MeasureTheory.Integrable (fun y ↦ GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) μ`. Introduce `F x`.

Establish `hc : Continuous fun y : G ↦ ψ (y⁻¹ * x)` using `hψ.comp (continuous_inv.mul continuous_const)`. Establish `hs : HasCompactSupport fun y : G ↦ ψ (y⁻¹ * x)` using `hψs.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))`. Simplify `(hloc F).integrable_smul_right_of_hasCompactSupport hc hs` using `[smul_eq_mul]`. Use `⟨hint, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `F F' s t`.

Use function extensionality and compare the values at `x`. Establish `hae : ∀ᵐ y ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑(s • F + t • F')) y = s * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y + t * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y`. Establish `h` using `Filter.Eventually.and (MeasureTheory.Lp.coeFn_add (s • F) (t • F')) (Filter.Eventually.and (MeasureTheory.Lp.coeFn_smul s F) (MeasureTheory.Lp.coeFn_smul t F'))`. Establish `h'` using `(GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff (μ := μ)).1 h`. Use `filter_upwards [h'] with y hy`.

Take `⟨e1, e2, e3⟩` from `hy`. Simplify using `only [GlobalTheory.AutomorphicL2Unitary.lift]`. Rewrite using `[e1, Pi.add_apply, e2, e3]`. Simplify using `[smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Unfold `UpperTheory.V.Cj.H.cv`. Use `MeasureTheory.integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with y hy`. Rewrite using `[hy]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = (s • cv ψ F + t • cv ψ F') x := by`. Rewrite using `[MeasureTheory.integral_add ((hint F x).const_mul s) ((hint F' x).const_mul t), MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]`. Simplify using `[UpperTheory.V.Cj.H.cv, smul_eq_mul]`. Introduce `F γ hγ g`. Unfold `UpperTheory.V.Cj.H.cv`.

Rewrite using `[← MeasureTheory.integral_mul_left_eq_self _ γ]`. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[GlobalTheory.AutomorphicL2Unitary.leftInv_lift _ γ hγ y, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]`. Introduce `C hC`.

Establish `hK : IsCompact (tsupport ψ)` using `hψs`. Take `⟨N, hN⟩` from `hcnt (C * (tsupport ψ)⁻¹) (hC.mul hK.inv)`. Use `⟨B * (N : ℝ), fun F x hx ↦ ?_⟩` and prove the remaining obligations. Use `hbd x N (fun g ↦ le_trans (Set.encard_le_encard ?_) (hN g)) F` and prove the remaining obligations. Introduce `γ hγ`.

Simplify using `only [Set.mem_setOf_eq] at hγ ⊢`. Establish `hmem : ((γ : G) * g)⁻¹ * x ∈ tsupport ψ` using `subset_tsupport _ (Function.mem_support.2 hγ)`. Establish `heq : (γ : G) * g = x * (((γ : G) * g)⁻¹ * x)⁻¹` using `by group`. Rewrite using `[heq]`. Conclude with `Set.mul_mem_mul hx (Set.inv_mem_inv.2 hmem)`.
-/
theorem UpperTheory.V.Cj.H.cvAlg :
    UpperTheory.V.Cj.H.CvAlg := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs
  obtain ⟨hloc, hcnt⟩ := locInt G Γ μ
  obtain ⟨B, hB, hbd⟩ := cvCount G Γ μ ψ hψ hψs
  have hint : ∀ (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (x : G),
      MeasureTheory.Integrable (fun y ↦ GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) μ := by
    intro F x
    have hc : Continuous fun y : G ↦ ψ (y⁻¹ * x) :=
      hψ.comp (continuous_inv.mul continuous_const)
    have hs : HasCompactSupport fun y : G ↦ ψ (y⁻¹ * x) :=
      hψs.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
    simpa [smul_eq_mul] using (hloc F).integrable_smul_right_of_hasCompactSupport hc hs
  refine ⟨hint, ?_, ?_, ?_⟩
  · intro F F' s t
    funext x
    have hae : ∀ᵐ y ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑(s • F + t • F')) y
        = s * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y + t * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y := by
      have h := Filter.Eventually.and (MeasureTheory.Lp.coeFn_add (s • F) (t • F'))
        (Filter.Eventually.and (MeasureTheory.Lp.coeFn_smul s F)
          (MeasureTheory.Lp.coeFn_smul t F'))
      have h' := (GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff (μ := μ)).1 h
      filter_upwards [h'] with y hy
      obtain ⟨e1, e2, e3⟩ := hy
      simp only [GlobalTheory.AutomorphicL2Unitary.lift]
      rw [e1, Pi.add_apply, e2, e3]
      simp [smul_eq_mul]
    calc cv ψ (s • F + t • F') x
        = ∫ y, (s * (GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x))
            + t * (GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y * ψ (y⁻¹ * x))) ∂μ := by
          unfold UpperTheory.V.Cj.H.cv
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hae] with y hy
          rw [hy]
          ring
      _ = (s • cv ψ F + t • cv ψ F') x := by
          rw [MeasureTheory.integral_add ((hint F x).const_mul s) ((hint F' x).const_mul t),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          simp [UpperTheory.V.Cj.H.cv, smul_eq_mul]
  · intro F γ hγ g
    unfold UpperTheory.V.Cj.H.cv
    rw [← MeasureTheory.integral_mul_left_eq_self _ γ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [GlobalTheory.AutomorphicL2Unitary.leftInv_lift _ γ hγ y, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · intro C hC
    have hK : IsCompact (tsupport ψ) := hψs
    obtain ⟨N, hN⟩ := hcnt (C * (tsupport ψ)⁻¹) (hC.mul hK.inv)
    refine ⟨B * (N : ℝ), fun F x hx ↦ ?_⟩
    refine hbd x N (fun g ↦ le_trans (Set.encard_le_encard ?_) (hN g)) F
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ ⊢
    have hmem : ((γ : G) * g)⁻¹ * x ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hγ)
    have heq : (γ : G) * g = x * (((γ : G) * g)⁻¹ * x)⁻¹ := by group
    rw [heq]
    exact Set.mul_mem_mul hx (Set.inv_mem_inv.2 hmem)
