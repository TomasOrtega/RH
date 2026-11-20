import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

noncomputable section

open MeasureTheory
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.ApproxUnit

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
-/
theorem avg_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (u : α → ℂ) (c : ℂ)
    (ε : ℝ) (hb0 : ∀ w, 0 ≤ b w) (hb1 : ∫ w, b w ∂μ = 1) (hum : AEStronglyMeasurable u μ)
    (h : ∀ w, b w ≠ 0 → ‖u w - c‖ ≤ ε) :
    ‖∫ w, u w * (b w : ℂ) ∂μ - c‖ ≤ ε := by
  have hbi : Integrable b μ := by
    by_contra hn
    rw [integral_undef hn] at hb1
    exact zero_ne_one hb1
  have hbc : Integrable (fun w => (b w : ℂ)) μ := hbi.ofReal
  have hpt : ∀ w, ‖(u w - c) * (b w : ℂ)‖ ≤ ε * b w := by
    intro w
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 w)]
    by_cases hw : b w = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_right (h w hw) (hb0 w)
  have hd : Integrable (fun w => (u w - c) * (b w : ℂ)) μ :=
    Integrable.mono' (hbi.const_mul ε)
      ((hum.sub aestronglyMeasurable_const).mul hbc.aestronglyMeasurable)
      (Filter.Eventually.of_forall hpt)
  have hc : ∫ w, (b w : ℂ) ∂μ = 1 := by
    rw [integral_complex_ofReal, hb1]
    simp
  have hu : Integrable (fun w => u w * (b w : ℂ)) μ := by
    have := hd.add (hbc.const_mul c)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]
    ring
  have e : ∫ w, u w * (b w : ℂ) ∂μ - c = ∫ w, (u w - c) * (b w : ℂ) ∂μ := by
    have h1 : (fun w => (u w - c) * (b w : ℂ)) = fun w => u w * (b w : ℂ) - c * (b w : ℂ) := by
      ext w
      ring
    rw [h1, integral_sub hu (hbc.const_mul c), integral_const_mul, hc, mul_one]
  rw [e]
  calc ‖∫ w, (u w - c) * (b w : ℂ) ∂μ‖ ≤ ∫ w, ε * b w ∂μ :=
        norm_integral_le_of_norm_le (hbi.const_mul ε) (Filter.Eventually.of_forall hpt)
    _ = ε := by rw [integral_const_mul, hb1, mul_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem cv_eq_avg (X : Ctx) (φ ψ : X.G → ℂ) (hψ : IsBump X ψ) (g : X.G) :
    cv X.μ φ ψ g = ∫ w, φ (g * w) * ((‖ψ w⁻¹‖ : ℝ) : ℂ) ∂X.μ := by
  unfold cv
  rw [← integral_mul_left_eq_self _ g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [mul_inv_rev, inv_mul_cancel_right]
  rw [← hψ.2.1]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cv_adj_eq_avg (X : Ctx) (f ψ : X.G → ℂ) (hψ : IsBump X ψ) (y : X.G) :
    cv X.μ (adj ψ) f y = ∫ z, f (z⁻¹ * y) * ((‖ψ z⁻¹‖ : ℝ) : ℂ) ∂X.μ := by
  unfold cv
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have h : adj ψ z = ((‖ψ z⁻¹‖ : ℝ) : ℂ) := by
    unfold adj
    rw [hψ.2.1 z⁻¹]
    simp
  simp only [h]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem approxU : CvTest → TwoUnif → ApproxU := by
  intro hcv htu X φ ε hφ hε
  obtain ⟨W₀, hW₀, hW⟩ := htu X φ ε hφ hε
  refine ⟨W₀ ∩ W₀⁻¹, Filter.inter_mem hW₀ (inv_mem_nhds_one _ hW₀), ?_⟩
  intro ψ hb hsub y
  have hsupp : ∀ w, ‖ψ w⁻¹‖ ≠ 0 → w ∈ W₀ ∧ w⁻¹ ∈ W₀ := by
    intro w hw
    have h1 : w⁻¹ ∈ tsupport ψ := subset_tsupport _ (norm_ne_zero_iff.1 hw)
    have h2 := hsub h1
    exact ⟨by simpa using h2.2, h2.1⟩
  have hb0 : ∀ w, 0 ≤ ‖ψ w⁻¹‖ := fun w => norm_nonneg _
  have key : ∀ z ∈ W₀, ‖cv X.μ φ ψ (z * y) - φ y‖ ≤ ε := by
    intro z hz
    rw [cv_eq_avg X φ ψ hb]
    refine avg_le X.μ (fun w => ‖ψ w⁻¹‖) (fun w => φ (z * y * w)) (φ y) ε hb0 hb.2.2
      (Continuous.aestronglyMeasurable (hφ.1.comp (by fun_prop))) ?_
    intro w hw
    exact hW z hz w (hsupp w hw).1 y
  refine ⟨?_, ?_⟩
  · simpa using key 1 (mem_of_mem_nhds hW₀)
  · rw [cv_adj_eq_avg X _ ψ hb]
    have hc : Continuous (cv X.μ φ ψ) := (hcv X φ ψ hφ hb.1).1.1
    refine avg_le X.μ (fun w => ‖ψ w⁻¹‖) (fun z => cv X.μ φ ψ (z⁻¹ * y)) (φ y) ε hb0 hb.2.2
      (Continuous.aestronglyMeasurable (hc.comp (by fun_prop))) ?_
    intro z hz
    exact key z⁻¹ (hsupp z hz).2

end GlobalTheory.CompanionTheory.ApproxUnit

end
