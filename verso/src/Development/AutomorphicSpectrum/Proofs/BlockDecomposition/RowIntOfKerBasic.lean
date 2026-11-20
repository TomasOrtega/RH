import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelRows

open PositivityTheory.Rg.BcB.E1

/- English proof (translation)
Introduce `hK X φ hφ`. Use `haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩`. Use `haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩`. Establish `hc : Continuous φ` using `hφ.1`. Establish `hcs : HasCompactSupport φ` using `hφ.2`.

Establish `hc' : Continuous fun z : X.G => φ z⁻¹` using `hc.comp continuous_inv`. Establish `hcs' : HasCompactSupport fun z : X.G => φ z⁻¹` using `hcs.comp_homeomorph (Homeomorph.inv X.G)`. Establish `hfin1 : ∫⁻ z, ‖φ z‖ₑ ∂X.μ ≠ ⊤` using `(hc.integrable_of_hasCompactSupport (μ := X.μ) hcs).2.ne`. Establish `hfin2 : ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ ≠ ⊤` using `(hc'.integrable_of_hasCompactSupport (μ := X.μ) hcs').2.ne`. Establish `hb` using `(hK X φ hφ).2.2.2.2.2`.

Establish `hν : X.ν = X.μ.restrict X.F` using `rfl`. Use `⟨∫⁻ z, ‖φ z‖ₑ ∂X.μ + ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ, ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hν, lintegral_tsum]`.

Use `tsum_congr fun γ => lintegral_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[Subgroup.smul_def, smul_eq_mul, mul_assoc]`. Introduce `γ`. Conclude with `(hc.comp (by fun_prop)).enorm.aemeasurable`. Use `_ = ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ := (X.fd.lintegral_eq_tsum'' (fun y => ‖φ (x⁻¹ * y)‖ₑ)).symm`.

Use `_ = ∫⁻ y, ‖φ y‖ₑ ∂X.μ := lintegral_mul_left_eq_self (fun y => ‖φ y‖ₑ) x⁻¹`. Use `_ ≤ _ := le_self_add`. Introduce `y`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hν, lintegral_tsum]`.

Introduce `γ`. Conclude with `(hc.comp (by fun_prop)).enorm.aemeasurable`. Use `_ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ ((γ • x)⁻¹ * y)‖ₑ ∂X.μ := by`. Rewrite using `[← (Equiv.inv X.Γ).tsum_eq]`. Use `tsum_congr fun γ => lintegral_congr fun x => ?_` and prove the remaining obligations.

Simplify using `[Subgroup.smul_def, smul_eq_mul, mul_inv_rev]`. Use `_ = ∫⁻ x, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ := (X.fd.lintegral_eq_tsum'' (fun x => ‖φ (x⁻¹ * y)‖ₑ)).symm`. Use `_ = ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ := by`. Rewrite using `[← lintegral_mul_left_eq_self (fun x => ‖φ (x⁻¹ * y)‖ₑ) y]`. Use `lintegral_congr fun z => ?_` and prove the remaining obligations.

Simplify using `[mul_inv_rev]`. Use `_ ≤ _ := le_add_self`.
-/
theorem rowInt_of_kerBasic : KerBasic → RowInt := by
  intro hK X φ hφ
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hc : Continuous φ := hφ.1
  have hcs : HasCompactSupport φ := hφ.2
  have hc' : Continuous fun z : X.G => φ z⁻¹ := hc.comp continuous_inv
  have hcs' : HasCompactSupport fun z : X.G => φ z⁻¹ :=
    hcs.comp_homeomorph (Homeomorph.inv X.G)
  have hfin1 : ∫⁻ z, ‖φ z‖ₑ ∂X.μ ≠ ⊤ :=
    (hc.integrable_of_hasCompactSupport (μ := X.μ) hcs).2.ne
  have hfin2 : ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ ≠ ⊤ :=
    (hc'.integrable_of_hasCompactSupport (μ := X.μ) hcs').2.ne
  have hb := (hK X φ hφ).2.2.2.2.2
  have hν : X.ν = X.μ.restrict X.F := rfl
  refine ⟨∫⁻ z, ‖φ z‖ₑ ∂X.μ + ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ, ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩, ?_, ?_⟩
  · intro x
    calc ∫⁻ y, ‖ker X.Γ φ x y‖ₑ ∂X.ν
        ≤ ∫⁻ y, ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.ν := lintegral_mono (hb x)
      _ = ∑' γ : X.Γ, ∫⁻ y in X.F, ‖φ (x⁻¹ * (γ • y))‖ₑ ∂X.μ := by
          rw [hν, lintegral_tsum]
          · refine tsum_congr fun γ => lintegral_congr fun y => ?_
            rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]
          · intro γ
            exact (hc.comp (by fun_prop)).enorm.aemeasurable
      _ = ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ :=
          (X.fd.lintegral_eq_tsum'' (fun y => ‖φ (x⁻¹ * y)‖ₑ)).symm
      _ = ∫⁻ y, ‖φ y‖ₑ ∂X.μ := lintegral_mul_left_eq_self (fun y => ‖φ y‖ₑ) x⁻¹
      _ ≤ _ := le_self_add
  · intro y
    calc ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ∂X.ν
        ≤ ∫⁻ x, ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.ν :=
          lintegral_mono fun x => hb x y
      _ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.μ := by
          rw [hν, lintegral_tsum]
          intro γ
          exact (hc.comp (by fun_prop)).enorm.aemeasurable
      _ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ ((γ • x)⁻¹ * y)‖ₑ ∂X.μ := by
          rw [← (Equiv.inv X.Γ).tsum_eq]
          refine tsum_congr fun γ => lintegral_congr fun x => ?_
          simp [Subgroup.smul_def, smul_eq_mul, mul_inv_rev]
      _ = ∫⁻ x, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ :=
          (X.fd.lintegral_eq_tsum'' (fun x => ‖φ (x⁻¹ * y)‖ₑ)).symm
      _ = ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ := by
          rw [← lintegral_mul_left_eq_self (fun x => ‖φ (x⁻¹ * y)‖ₑ) y]
          refine lintegral_congr fun z => ?_
          simp [mul_inv_rev]
      _ ≤ _ := le_add_self

end GlobalTheory.CompanionTheory.KernelRows
