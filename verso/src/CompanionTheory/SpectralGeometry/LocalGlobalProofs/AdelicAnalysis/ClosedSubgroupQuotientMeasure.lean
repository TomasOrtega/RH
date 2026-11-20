import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

noncomputable def closedEmbeddingRangeEquiv {G G₁ : Type} [Group G] [TopologicalSpace G]
    [Group G₁] [TopologicalSpace G₁] (ι : G₁ →* G) (hι : IsClosedEmbedding ι) :
    G₁ ≃ₜ* ι.range :=
  have hemb : IsEmbedding ι.rangeRestrict :=
    IsEmbedding.of_comp (hι.continuous.subtype_mk _) continuous_subtype_val hι.isEmbedding
  { MulEquiv.ofBijective ι.rangeRestrict
      ⟨hemb.injective, ι.rangeRestrict_surjective⟩ with
    continuous_toFun := hemb.continuous
    continuous_invFun :=
      (hemb.toHomeomorphOfSurjective ι.rangeRestrict_surjective).symm.continuous }

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hι μ₁ _ _`. Establish `hclosed : IsClosed ((ι.range : Subgroup G) : Set G)`. Rewrite using `[MonoidHom.coe_range]`. Conclude with `hι.isClosed_range`. Set `e : G₁ ≃ₜ* ι.range` to `closedEmbeddingRangeEquiv ι hι`.

Use `haveI : IsFiniteMeasureOnCompacts μ₁.inv := ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩`. Use `haveI : μ₁.inv.IsOpenPosMeasure := ⟨fun U hU hne => by`. Rewrite using `[Measure.inv_apply]`. Conclude with `hU.inv.measure_ne_zero μ₁ hne.inv⟩`. Use `haveI hinv : μ₁.inv.IsHaarMeasure := {}`.

Establish `hν : (μ₁.inv.map e).IsHaarMeasure` using `ContinuousMulEquiv.isHaarMeasure_map μ₁.inv e`. Take `⟨β, hβ, hmass⟩` from `PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat G ι.range hclosed _ hν`. Use `⟨fun g => β g⁻¹, hβ.comp measurable_inv, fun g => ?_⟩` and prove the remaining obligations. Establish `hem : Measurable e` using `e.continuous.measurable`. Establish `hf : Measurable fun h : ι.range => β (g⁻¹ * (h : G))` using `hβ.comp (measurable_const.mul measurable_subtype_coe)`.

Establish `h1` using `hmass g⁻¹`. Establish `hcomp : Measurable fun a : G₁ => β (g⁻¹ * (e a : G))` using `hf.comp hem`. Rewrite `h1` using `[lintegral_map hf hem, Measure.inv, lintegral_map hcomp measurable_inv]`. Use `Eq.trans (lintegral_congr fun u => ?_) h1` and prove the remaining obligations. Establish `: ((e u⁻¹ : ι.range) : G) = (ι u)⁻¹` using `by show ι u⁻¹ = _`.

Conclude with `map_inv ι u`. Use `show β (ι u * g)⁻¹ = β (g⁻¹ * ((e u⁻¹ : ι.range) : G))`. Rewrite using `[this, mul_inv_rev]`.
-/
theorem exists_weight_mass_one_right_coset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  intro G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hι μ₁ _ _
  have hclosed : IsClosed ((ι.range : Subgroup G) : Set G) := by
    rw [MonoidHom.coe_range]; exact hι.isClosed_range
  let e : G₁ ≃ₜ* ι.range := closedEmbeddingRangeEquiv ι hι
  haveI : IsFiniteMeasureOnCompacts μ₁.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  haveI : μ₁.inv.IsOpenPosMeasure :=
    ⟨fun U hU hne => by
      rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero μ₁ hne.inv⟩
  haveI hinv : μ₁.inv.IsHaarMeasure := {}
  have hν : (μ₁.inv.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ₁.inv e
  obtain ⟨β, hβ, hmass⟩ := PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat G ι.range hclosed _ hν
  refine ⟨fun g => β g⁻¹, hβ.comp measurable_inv, fun g => ?_⟩
  have hem : Measurable e := e.continuous.measurable
  have hf : Measurable fun h : ι.range => β (g⁻¹ * (h : G)) :=
    hβ.comp (measurable_const.mul measurable_subtype_coe)
  have h1 := hmass g⁻¹
  have hcomp : Measurable fun a : G₁ => β (g⁻¹ * (e a : G)) := hf.comp hem
  rw [lintegral_map hf hem, Measure.inv, lintegral_map hcomp measurable_inv] at h1
  refine Eq.trans (lintegral_congr fun u => ?_) h1
  have : ((e u⁻¹ : ι.range) : G) = (ι u)⁻¹ := by
    show ι u⁻¹ = _
    exact map_inv ι u
  show β (ι u * g)⁻¹ = β (g⁻¹ * ((e u⁻¹ : ι.range) : G))
  rw [this, mul_inv_rev]

end GlobalTheory.CompanionTheory.SW
