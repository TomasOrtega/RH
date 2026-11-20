import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSetOfSmulMemEqZero
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

/- English proof (translation)
Use `haveI : MeasurableConstSMul Γ X := ⟨fun c => (measurable_const_smul (c : S) : Measurable fun x : X => (c : S) • x)⟩`. Use `haveI : SMulInvariantMeasure Γ X μ := ⟨fun c A hA => SMulInvariantMeasure.measure_preimage_smul (c : S) hA⟩`. Use `haveI : MeasurableConstSMul Γ S := ⟨fun c => (measurable_const_mul (c : S) : Measurable fun x : S => (c : S) * x)⟩`. Use `haveI : SMulInvariantMeasure Γ S ν := ⟨fun c A _ => measure_preimage_mul ν (c : S) A⟩`. Use `set F : X → ℝ≥0∞ := fun y => ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) with hF`.

Establish `hQ : MeasurableSet {p : X × S | p.2 ∈ E ∧ p.2⁻¹ • p.1 ∈ D₁}` using `(measurable_snd hE).inter (hD₁.preimage (measurable_snd.inv.smul measurable_fst))`. Establish `hmeasν : Measurable fun y : X => ν (E ∩ {s | s⁻¹ • y ∈ D₁})`. Use `measurable_measure_prodMk_left (ν := ν) hQ` as an intermediate fact. Conclude with `this`. Establish `hFm : Measurable F` using `hψ.mul hmeasν`.

Establish `hstep : ∀ y : X, ∑' γ : Γ, F (γ • y) = ψ y * ν {s | s⁻¹ • y ∈ D₁}`. Introduce `y`. Establish `h1 : ∀ γ : Γ, F (γ • y) = ψ y * ν (E ∩ {s | s⁻¹ • ((γ : S) • y) ∈ D₁})`. Introduce `γ`. Simplify using `only [hF, Subgroup.smul_def, hinv]`.

Repeatedly rewrite using `[h1]`. Rewrite using `[ENNReal.tsum_mul_left]`. Use `congr 1`. Rewrite using `[hEf.measure_eq_tsum {s | s⁻¹ • y ∈ D₁}]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `s`. Simplify using `only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, mul_inv_rev, inv_inv, mul_smul]`. Conclude with `and_comm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[lintegral_tsum]`. Introduce `γ`. Conclude with `(hFm.comp (measurable_const_smul γ)).aemeasurable`. Use `_ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by`. Repeatedly rewrite using `[hstep]`.
-/
theorem lintegral_unfold_refold (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X]
    [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
  haveI : MeasurableConstSMul Γ X :=
    ⟨fun c => (measurable_const_smul (c : S) : Measurable fun x : X => (c : S) • x)⟩
  haveI : SMulInvariantMeasure Γ X μ :=
    ⟨fun c A hA => SMulInvariantMeasure.measure_preimage_smul (c : S) hA⟩
  haveI : MeasurableConstSMul Γ S :=
    ⟨fun c => (measurable_const_mul (c : S) : Measurable fun x : S => (c : S) * x)⟩
  haveI : SMulInvariantMeasure Γ S ν :=
    ⟨fun c A _ => measure_preimage_mul ν (c : S) A⟩
  set F : X → ℝ≥0∞ := fun y => ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) with hF
  have hQ : MeasurableSet {p : X × S | p.2 ∈ E ∧ p.2⁻¹ • p.1 ∈ D₁} :=
    (measurable_snd hE).inter (hD₁.preimage (measurable_snd.inv.smul measurable_fst))
  have hmeasν : Measurable fun y : X => ν (E ∩ {s | s⁻¹ • y ∈ D₁}) := by
    have := measurable_measure_prodMk_left (ν := ν) hQ
    exact this
  have hFm : Measurable F := hψ.mul hmeasν
  have hstep : ∀ y : X, ∑' γ : Γ, F (γ • y) = ψ y * ν {s | s⁻¹ • y ∈ D₁} := by
    intro y
    have h1 : ∀ γ : Γ, F (γ • y) = ψ y * ν (E ∩ {s | s⁻¹ • ((γ : S) • y) ∈ D₁}) := by
      intro γ
      simp only [hF, Subgroup.smul_def, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left]
    congr 1
    rw [hEf.measure_eq_tsum {s | s⁻¹ • y ∈ D₁}]
    refine tsum_congr fun γ => ?_
    congr 1
    ext s
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_setOf_eq,
      Subgroup.smul_def, smul_eq_mul, mul_inv_rev, inv_inv, mul_smul]
    exact and_comm
  calc ∫⁻ y, F y ∂μ = ∑' γ : Γ, ∫⁻ y in D₂, F (γ • y) ∂μ := hD₂.lintegral_eq_tsum'' F
    _ = ∫⁻ y in D₂, ∑' γ : Γ, F (γ • y) ∂μ := by
      rw [lintegral_tsum]
      intro γ
      exact (hFm.comp (measurable_const_smul γ)).aemeasurable
    _ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ := by
      simp_rw [hstep]

end GlobalTheory.CovolIndep
