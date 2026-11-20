import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldMult

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PI.PoincareSeriesMemLp.UnitaryGroupMassFormula

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

/- English proof (translation)
Establish `hsum : ∀ x, Summable (fun δ : D => Ph ((δ : G) * x))`. Introduce `x`. Establish `h1 : Summable (fun δ : D => ‖Ph ((δ : G) * x)‖₊)`. Establish `h2` using `hs x`. Simplify using `only [enorm_eq_nnnorm] at h2`.

Conclude with `ENNReal.tsum_coe_ne_top_iff_summable.mp h2`. Conclude with `Summable.of_norm (by simpa using NNReal.summable_coe.mpr h1)`. Use `measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset D)) (f := fun (s : Finset D) x => ∑ δ ∈ s, Ph ((δ : G) * x)) (fun s => ?_) ?_` and prove the remaining obligations. Conclude with `Finset.measurable_sum _ (fun δ _ => hPh.comp (measurable_const_mul _))`. Rewrite using `[tendsto_pi_nhds]`.

Introduce `x`. Unfold `poinc`. Conclude with `(hsum x).hasSum`.
-/
theorem measurable_poinc {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (D : Set G) [Countable D] (Ph : G → ℂ) (hPh : Measurable Ph)
    (hs : ∀ x, (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) ≠ ⊤) : Measurable (poinc D Ph) := by
  have hsum : ∀ x, Summable (fun δ : D => Ph ((δ : G) * x)) := by
    intro x
    have h1 : Summable (fun δ : D => ‖Ph ((δ : G) * x)‖₊) := by
      have h2 := hs x
      simp only [enorm_eq_nnnorm] at h2
      exact ENNReal.tsum_coe_ne_top_iff_summable.mp h2
    exact Summable.of_norm (by simpa using NNReal.summable_coe.mpr h1)
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset D))
    (f := fun (s : Finset D) x => ∑ δ ∈ s, Ph ((δ : G) * x)) (fun s => ?_) ?_
  · exact Finset.measurable_sum _ (fun δ _ => hPh.comp (measurable_const_mul _))
  · rw [tendsto_pi_nhds]
    intro x
    unfold poinc
    exact (hsum x).hasSum

/- English proof (translation)
Introduce `Γ S hΓ hSΓ Ω hΩ h1 a Ph hdat F hF hI D hD FΓ hFΓ`. Take `⟨hPh, hinv, hrep⟩` from `hdat`. Establish `hcΓ : Countable Γ` using `(TopologicalSpace.separableSpace_iff_countable (α := Γ)).mp inferInstance`. Establish `hcD : Countable D`. Establish `hinj : Function.Injective (fun d : D => (⟨d.1, hD.1 d.2⟩ : Γ))`.

Introduce `d e h`. Conclude with `Subtype.ext (by simpa using congrArg Subtype.val h)`. Conclude with `hinj.countable`. Take `⟨hm1, hmtop, hminv, hmmeas⟩` from `overlapMultiplicityProperties G Γ hΓ Ω hΩ h1`. Establish `hqI : quotientLIntegral μ F Ph ≤ multiplicityLIntegral μ Γ Ω F Ph`.

Unfold `quotientLIntegral multiplicityLIntegral`. Conclude with `lintegral_mono fun y => le_mul_of_one_le_left (by simp) (hm1 y)`. Establish `hq : quotientLIntegral μ F Ph < ⊤` using `lt_of_le_of_lt hqI hI`. Establish `hT : ∀ x : G, ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≤ (a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph` using `fun x => foldBound_holds G μ Γ S hΓ hSΓ Ω hΩ.measurableSet a Ph hPh hinv hrep F hF D hD x`. Establish `hTfin : ∀ x : G, ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≠ ⊤` using `fun x => ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (hmtop x).ne) hq.ne) (hT x)`.

Use `set g : G → ℝ≥0∞ := fun y => mult Γ Ω y * ‖Ph y‖ₑ with hgdef`. Establish `hpt : ∀ x : G, ‖poinc D Ph x‖ₑ ^ 2 ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∑' δ : D, g ((δ : G) * x)`. Introduce `x`. Establish `hP : ‖poinc D Ph x‖ₑ ≤ ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ` using `enorm_tsum_le_tsum_enorm`. Establish `hg : ∑' δ : D, g ((δ : G) * x) = mult Γ Ω x * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ`.

Rewrite using `[← ENNReal.tsum_mul_left]`. Use `tsum_congr fun δ => ?_` and prove the remaining obligations. Simplify using `only [hgdef]`. Rewrite using `[hminv δ (hD.1 δ.2) x]`. Rewrite using `[hg, pow_two]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hgm : Measurable g` using `hmmeas.mul hPh.enorm`. Establish `hginv : ∀ s ∈ S, ∀ y : G, g (s * y) = g y`. Introduce `s hs y`. Simplify using `only [hgdef]`.

Rewrite using `[hminv s (hSΓ hs) y, hinv s hs y]`. Establish `hunf : (∫⁻ x in FΓ, ∑' δ : D, g ((δ : G) * x) ∂μ) = multiplicityLIntegral μ Γ Ω F Ph` using `lintegralTransversalSum G μ Γ S hSΓ F hF FΓ hFΓ D hD g hgm hginv`. Establish `hbound : (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ) ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph`. Combine the equalities or inequalities in the displayed calculation. Establish `hlast : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph ≤ (a : ℝ≥0∞) * multiplicityLIntegral μ Γ Ω F Ph ^ 2`.

Rewrite using `[pow_two, ← mul_assoc]`. Conclude with `mul_le_mul' (mul_le_mul' le_rfl hqI) le_rfl`. Establish `hfin : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph < ⊤` using `ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hq) hI`. Establish `hPm : Measurable (poinc D Ph)` using `measurable_poinc D Ph hPh hTfin`. Use `⟨⟨hPm.aestronglyMeasurable, ?_⟩, hbound, hlast⟩` and prove the remaining obligations.

Rewrite using `[eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]`. Establish `h2 : ∀ x, ‖poinc D Ph x‖ₑ ^ ((2 : ℝ≥0∞).toReal) = ‖poinc D Ph x‖ₑ ^ 2`. Introduce `x`. Rewrite using `[ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]`. Evaluate the numerical expressions.

Repeatedly rewrite using `[h2]`. Conclude with `lt_of_le_of_lt hbound hfin`.
-/
theorem fold_L2_double_coset (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesMemLp G μ := by
  intro Γ S hΓ hSΓ Ω hΩ h1 a Ph hdat F hF hI D hD FΓ hFΓ
  obtain ⟨hPh, hinv, hrep⟩ := hdat
  have hcΓ : Countable Γ :=
    (TopologicalSpace.separableSpace_iff_countable (α := Γ)).mp inferInstance
  have hcD : Countable D := by
    have hinj : Function.Injective (fun d : D => (⟨d.1, hD.1 d.2⟩ : Γ)) := by
      intro d e h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    exact hinj.countable
  obtain ⟨hm1, hmtop, hminv, hmmeas⟩ := overlapMultiplicityProperties G Γ hΓ Ω hΩ h1

  have hqI : quotientLIntegral μ F Ph ≤ multiplicityLIntegral μ Γ Ω F Ph := by
    unfold quotientLIntegral multiplicityLIntegral
    exact lintegral_mono fun y => le_mul_of_one_le_left (by simp) (hm1 y)
  have hq : quotientLIntegral μ F Ph < ⊤ := lt_of_le_of_lt hqI hI

  have hT : ∀ x : G, ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≤ (a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph :=
    fun x => foldBound_holds G μ Γ S hΓ hSΓ Ω hΩ.measurableSet a Ph hPh hinv hrep F hF D hD x
  have hTfin : ∀ x : G, ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (hmtop x).ne) hq.ne) (hT x)
  set g : G → ℝ≥0∞ := fun y => mult Γ Ω y * ‖Ph y‖ₑ with hgdef
  have hpt : ∀ x : G, ‖poinc D Ph x‖ₑ ^ 2
      ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∑' δ : D, g ((δ : G) * x) := by
    intro x
    have hP : ‖poinc D Ph x‖ₑ ≤ ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := enorm_tsum_le_tsum_enorm
    have hg : ∑' δ : D, g ((δ : G) * x) = mult Γ Ω x * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun δ => ?_
      simp only [hgdef]
      rw [hminv δ (hD.1 δ.2) x]
    rw [hg, pow_two]
    calc ‖poinc D Ph x‖ₑ * ‖poinc D Ph x‖ₑ
        ≤ (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ := mul_le_mul' hP hP
      _ ≤ (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) * ((a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph) :=
          mul_le_mul' le_rfl (hT x)
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * (mult Γ Ω x * ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) := by ring

  have hgm : Measurable g := hmmeas.mul hPh.enorm
  have hginv : ∀ s ∈ S, ∀ y : G, g (s * y) = g y := by
    intro s hs y
    simp only [hgdef]
    rw [hminv s (hSΓ hs) y, hinv s hs y]
  have hunf : (∫⁻ x in FΓ, ∑' δ : D, g ((δ : G) * x) ∂μ) = multiplicityLIntegral μ Γ Ω F Ph :=
    lintegralTransversalSum G μ Γ S hSΓ F hF FΓ hFΓ D hD g hgm hginv
  have hbound : (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ)
      ≤ (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph := by
    calc (∫⁻ x in FΓ, ‖poinc D Ph x‖ₑ ^ 2 ∂μ)
        ≤ ∫⁻ x in FΓ, (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∑' δ : D, g ((δ : G) * x) ∂μ :=
          lintegral_mono hpt
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * ∫⁻ x in FΓ, ∑' δ : D, g ((δ : G) * x) ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hq.ne)
      _ = (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph := by rw [hunf]

  have hlast : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph
      ≤ (a : ℝ≥0∞) * multiplicityLIntegral μ Γ Ω F Ph ^ 2 := by
    rw [pow_two, ← mul_assoc]
    exact mul_le_mul' (mul_le_mul' le_rfl hqI) le_rfl

  have hfin : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F Ph < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hq) hI
  have hPm : Measurable (poinc D Ph) := measurable_poinc D Ph hPh hTfin
  refine ⟨⟨hPm.aestronglyMeasurable, ?_⟩, hbound, hlast⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have h2 : ∀ x, ‖poinc D Ph x‖ₑ ^ ((2 : ℝ≥0∞).toReal) = ‖poinc D Ph x‖ₑ ^ 2 := by
    intro x
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]
    norm_num
  simp_rw [h2]
  exact lt_of_le_of_lt hbound hfin

end PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
