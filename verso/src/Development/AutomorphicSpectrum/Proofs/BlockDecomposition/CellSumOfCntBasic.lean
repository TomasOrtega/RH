import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.CellSumProof

noncomputable def hits (X : Ctx) (S : Set X.G) (x : X.G) : ℝ≥0∞ :=
  ∑' γ : X.Γ, S.indicator 1 ((γ : X.G) * x)

/- English proof (translation)
Unfold `hits`. Use `Measurable.ennreal_tsum fun γ => ?_` and prove the remaining obligations. Conclude with `(measurable_one.indicator hS).comp (measurable_const_mul (γ : X.G))`.
-/
theorem measurable_hits (X : Ctx) {S : Set X.G} (hS : MeasurableSet S) :
    Measurable (hits X S) := by
  unfold hits
  refine Measurable.ennreal_tsum fun γ => ?_
  exact (measurable_one.indicator hS).comp (measurable_const_mul (γ : X.G))

/- English proof (translation)
Use `haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩`. Use `haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩`. Establish `hm : ∀ γ : X.Γ, AEMeasurable (fun x : X.G => S.indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x)) X.ν` using `fun γ => ((measurable_one.indicator hS).comp (measurable_const_mul (γ : X.G))).aemeasurable`. Establish `h1 : ∫⁻ x, hits X S x ∂X.ν = ∑' γ : X.Γ, ∫⁻ x in X.F, S.indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x) ∂X.μ`. Unfold `hits`.

Conclude with `lintegral_tsum hm`. Establish `h2` using `X.fd.lintegral_eq_tsum'' (S.indicator (1 : X.G → ℝ≥0∞))`. Rewrite using `[h1]`. Establish `h3 : ∫⁻ x, S.indicator (1 : X.G → ℝ≥0∞) x ∂X.μ = X.μ S` using `lintegral_indicator_one hS`. Rewrite using `[← h3, h2]`.

Both sides reduce to the same expression.
-/
theorem lintegral_hits (X : Ctx) {S : Set X.G} (hS : MeasurableSet S) :
    ∫⁻ x, hits X S x ∂X.ν = X.μ S := by
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hm : ∀ γ : X.Γ, AEMeasurable (fun x : X.G => S.indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x)) X.ν :=
    fun γ => ((measurable_one.indicator hS).comp (measurable_const_mul (γ : X.G))).aemeasurable
  have h1 : ∫⁻ x, hits X S x ∂X.ν
      = ∑' γ : X.Γ, ∫⁻ x in X.F, S.indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x) ∂X.μ := by
    unfold hits
    exact lintegral_tsum hm
  have h2 := X.fd.lintegral_eq_tsum'' (S.indicator (1 : X.G → ℝ≥0∞))
  rw [h1]
  have h3 : ∫⁻ x, S.indicator (1 : X.G → ℝ≥0∞) x ∂X.μ = X.μ S := lintegral_indicator_one hS
  rw [← h3, h2]
  rfl

/- English proof (translation)
Unfold `cnt hits`. Set `e : X.Γ ≃ X.Γ` to `Equiv.mulLeft (⟨δ, hδ⟩ : X.Γ)`. Rewrite using `[← e.tsum_eq (fun γ : X.Γ => (a • (Ω₀ * Ω)).indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x))]`. Use `ENNReal.tsum_le_tsum fun γ => ?_` and prove the remaining obligations. Distinguish the cases in `h : x⁻¹ * (γ : X.G) * x ∈ Ω`.

Establish `hmem : ((e γ : X.Γ) : X.G) * x ∈ a • (Ω₀ * Ω)`. Use `Set.mem_smul_set.2 ⟨o * (x⁻¹ * (γ : X.G) * x), Set.mul_mem_mul ho h, ?_⟩` and prove the remaining obligations. Establish `: ((e γ : X.Γ) : X.G) = δ * (γ : X.G)` using `rfl`. Rewrite using `[this, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← hx]`. Use `group`.

Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem hmem]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem h]`. Conclude with `bot_le`.
-/
theorem cnt_le_hits (X : Ctx) {Ω₀ Ω : Set X.G} {δ a o x : X.G} (hδ : δ ∈ X.Γ) (ho : o ∈ Ω₀)
    (hx : δ * x = a * o) : cnt X.Γ Ω x ≤ hits X (a • (Ω₀ * Ω)) x := by
  unfold cnt hits
  let e : X.Γ ≃ X.Γ := Equiv.mulLeft (⟨δ, hδ⟩ : X.Γ)
  rw [← e.tsum_eq (fun γ : X.Γ => (a • (Ω₀ * Ω)).indicator (1 : X.G → ℝ≥0∞) ((γ : X.G) * x))]
  refine ENNReal.tsum_le_tsum fun γ => ?_
  by_cases h : x⁻¹ * (γ : X.G) * x ∈ Ω
  · have hmem : ((e γ : X.Γ) : X.G) * x ∈ a • (Ω₀ * Ω) := by
      refine Set.mem_smul_set.2 ⟨o * (x⁻¹ * (γ : X.G) * x), Set.mul_mem_mul ho h, ?_⟩
      have : ((e γ : X.Γ) : X.G) = δ * (γ : X.G) := rfl
      rw [this, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← hx]
      group
    rw [Set.indicator_of_mem h, Set.indicator_of_mem hmem]
    simp
  · rw [Set.indicator_of_notMem h]
    exact bot_le

/- English proof (translation)
Introduce `X ι _ a Ω₀ Ω w c h₀ hΩ hcov hw hc`. Establish `hcomp : IsCompact (Ω₀ * Ω)` using `h₀.mul hΩ`. Establish `hmeas : ∀ i, MeasurableSet (a i • (Ω₀ * Ω))` using `fun i => (hcomp.smul (a i)).measurableSet`. Establish `hpt : ∀ x, w x * cnt X.Γ Ω x ≤ ∑' i, c i * hits X (a i • (Ω₀ * Ω)) x`. Introduce `x`.

Take `⟨δ, hδ, i, o, ho, hx⟩` from `hcov x`. Establish `hwx : w x ≤ c i`. Rewrite using `[← hw δ hδ x, hx]`. Conclude with `hc i o ho`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Use `tsum_congr fun i => ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul _ (measurable_hits X (hmeas i)), lintegral_hits X (hmeas i), measure_smul]`. Use `_ = X.μ (Ω₀ * Ω) * ∑' i, c i := by`. Rewrite using `[ENNReal.tsum_mul_right, mul_comm]`.
-/
theorem cellSum_holds : CellSum := by
  intro X ι _ a Ω₀ Ω w c h₀ hΩ hcov hw hc
  have hcomp : IsCompact (Ω₀ * Ω) := h₀.mul hΩ
  have hmeas : ∀ i, MeasurableSet (a i • (Ω₀ * Ω)) := fun i =>
    (hcomp.smul (a i)).measurableSet
  have hpt : ∀ x, w x * cnt X.Γ Ω x ≤ ∑' i, c i * hits X (a i • (Ω₀ * Ω)) x := by
    intro x
    obtain ⟨δ, hδ, i, o, ho, hx⟩ := hcov x
    have hwx : w x ≤ c i := by
      rw [← hw δ hδ x, hx]
      exact hc i o ho
    calc w x * cnt X.Γ Ω x ≤ c i * hits X (a i • (Ω₀ * Ω)) x :=
          mul_le_mul' hwx (cnt_le_hits X hδ ho hx)
      _ ≤ _ := ENNReal.le_tsum i
  calc ∫⁻ x, w x * cnt X.Γ Ω x ∂X.ν
      ≤ ∫⁻ x, ∑' i, c i * hits X (a i • (Ω₀ * Ω)) x ∂X.ν := lintegral_mono hpt
    _ = ∑' i, ∫⁻ x, c i * hits X (a i • (Ω₀ * Ω)) x ∂X.ν :=
        lintegral_tsum fun i => ((measurable_hits X (hmeas i)).const_mul _).aemeasurable
    _ = ∑' i, c i * X.μ (Ω₀ * Ω) := by
        refine tsum_congr fun i => ?_
        rw [lintegral_const_mul _ (measurable_hits X (hmeas i)), lintegral_hits X (hmeas i),
          measure_smul]
    _ = X.μ (Ω₀ * Ω) * ∑' i, c i := by
        rw [ENNReal.tsum_mul_right, mul_comm]

/- English proof (translation)
Introduce `_` and use `cellSum_holds`.
-/
theorem cellSum_of_cntBasic : CntBasic → CellSum := fun _ => cellSum_holds

end GlobalTheory.CompanionTheory.CellSumProof
