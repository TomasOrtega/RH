import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.CV

namespace QuotientIntegral

/- English proof (translation)
Rewrite using `[← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]`. Conclude with `ENNReal.ofReal_toReal_le`.
-/
theorem enorm_ofReal_toReal_le (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `: LocallyCompactSpace T` using `hT.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology T` using `TopologicalSpace.Subtype.secondCountableTopology (T : Set G)`. Establish `: SigmaCompactSpace T` using `inferInstance`. Establish `: SFinite ν` using `inferInstance`. Establish `hmcoe : Measurable (fun h : T => (h : G))` using `measurable_subtype_coe`.

Establish `: ν.IsMulRightInvariant`. Establish `: ν.inv.IsMulRightInvariant` using `inferInstance`. Rewrite `this` using `[Measure.inv_eq_self]`. Then use the resulting hypothesis. Take `⟨U, hUc, hU1⟩` from `exists_compact_mem_nhds (1 : G)`. Use `set K : Set G := U * C with hKdef`.

Establish `hKc : IsCompact K` using `hUc.mul hC`. Establish `hKm : MeasurableSet K` using `hKc.isClosed.measurableSet`. Use `set S : Set G := (T : Set G) * C with hSdef`. Establish `hSm : MeasurableSet S` using `(hT.mul_right_of_isCompact hC).measurableSet`. Establish `hSinv : ∀ t ∈ T, ∀ x, t * x ∈ S ↔ x ∈ S`.

Introduce `t ht x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, c, hc, hsc⟩`. Conclude with `⟨t⁻¹ * s, T.mul_mem (T.inv_mem ht) hs, c, hc, by show t⁻¹ * s * c = x`. Rewrite using `[mul_assoc, show s * c = t * x from hsc, inv_mul_cancel_left]⟩`.

Introduce and unpack `⟨s, hs, c, hc, rfl⟩`. Conclude with `⟨t * s, T.mul_mem ht hs, c, hc, mul_assoc _ _ _⟩`. Establish `hKind : Measurable (K.indicator (1 : G → ℝ≥0∞))` using `measurable_one.indicator hKm`. Use `set I : G → ℝ≥0∞ := fun g => ∫⁻ h : T, K.indicator 1 ((h : G) * g) ∂ν with hIdef`. Establish `hIm : Measurable I`.

Establish `: Measurable (fun p : G × T => K.indicator (1 : G → ℝ≥0∞) ((p.2 : G) * p.1))` using `hKind.comp ((hmcoe.comp measurable_snd).mul measurable_fst)`. Conclude with `this.lintegral_prod_right'`. Establish `hIT : ∀ t ∈ T, ∀ g, I (t * g) = I g`. Introduce `t ht g`. Use `lintegral_mul_right_eq_self (μ := ν) (fun h : T => K.indicator (1 : G → ℝ≥0∞) ((h : G) * g)) ⟨t, ht⟩` as an intermediate fact.

Simplify using `only [hIdef]`. Rewrite using `[← this]`. Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Simplify using `[mul_assoc]`. Use `set V : Set T := (fun h : T => (h : G)) ⁻¹' interior U with hVdef`.

Establish `hVm : MeasurableSet V` using `hmcoe measurableSet_interior`. Establish `hVpos : ν V ≠ 0`. Establish `hVo : IsOpen V` using `isOpen_interior.preimage continuous_subtype_val`. Establish `h1 : (1 : T) ∈ V` using `by show ((1 : T) : G) ∈ interior U`. Simplify using `using mem_interior_iff_mem_nhds.mpr hU1`.

Conclude with `(hVo.measure_pos ν ⟨1, h1⟩).ne'`. Establish `hIC : ∀ g ∈ S, ν V ≤ I g`. Introduce and unpack `_ ⟨t, ht, c, hc, rfl⟩`. Rewrite using `[hIT t ht c, ← lintegral_indicator_one hVm]`. Use `lintegral_mono fun h => ?_` and prove the remaining obligations.

Distinguish the cases in `hh : h ∈ V`. Establish `hK : (h : G) * c ∈ K` using `Set.mul_mem_mul (interior_subset hh) hc`. Simplify using `[hh, hK]`. Simplify using `[Set.indicator_apply, hh]`. Establish `hIfin : ∀ g, I g ≠ ⊤`.

Introduce `g`. Establish `hemb : Topology.IsClosedEmbedding (fun h : T => (h : G) * g)` using `(Homeomorph.mulRight g).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal`. Establish `hmeas : Measurable (fun h : T => (h : G) * g)` using `hmcoe.mul_const g`. Establish `: I g = ν ((fun h : T => (h : G) * g) ⁻¹' K)`. Rewrite using `[← lintegral_indicator_one (hmeas hKm)]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `((hemb.isCompact_preimage hKc).measure_lt_top).ne`. Use `set ρ : G → ℝ≥0∞ := S.piecewise (fun g => K.indicator 1 g * (I g)⁻¹) ρ0 with hρdef`. Establish `hρ : IsQuotNormaliser T ν ρ`.

Use `⟨Measurable.piecewise hSm (hKind.mul hIm.inv) h0.1, fun g => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ S`. Establish `hmem : ∀ h : T, (h : G) * g ∈ S` using `fun h => (hSinv _ h.2 g).2 hg`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun h => ?_` and prove the remaining obligations.

Simplify using `only [hρdef, Set.piecewise_eq_of_mem _ _ _ (hmem h), hIT _ h.2]`. Use `_ = I g * (I g)⁻¹ := lintegral_mul_const _ (hKind.comp (hmcoe.mul_const g))`. Use `_ = 1 := ENNReal.mul_inv_cancel (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hVpos) (hIC g hg))) (hIfin g)`. Establish `hmem : ∀ h : T, (h : G) * g ∉ S` using `fun h hh => hg ((hSinv _ h.2 g).1 hh)`. Rewrite using `[← h0.2 g]`.

Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Simplify using `only [hρdef, Set.piecewise_eq_of_notMem _ _ _ (hmem h)]`. Establish `hF1 : Measurable (S.indicator (1 : G → ℝ≥0∞))` using `measurable_one.indicator hSm`. Establish `hFinv : ∀ h ∈ T, ∀ g, S.indicator (1 : G → ℝ≥0∞) (h * g) = S.indicator 1 g`. Introduce `h hh g`.

Simplify using `only [Set.indicator_apply, hSinv h hh g, Pi.one_apply]`. Rewrite using `[lintegral_normaliser_eq hF1 hFinv h0 hρ]`. Use `ne_of_lt (lt_of_le_of_lt (b := ∫⁻ g, K.indicator 1 g * (ν V)⁻¹ ∂μ) (lintegral_mono fun g => ?_) ?_)` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ S`. Simplify using `only [Set.indicator_of_mem hg, Pi.one_apply, one_mul, hρdef, Set.piecewise_eq_of_mem _ _ _ hg] gcongr`.

Conclude with `hIC g hg`. Simplify using `[hg]`. Rewrite using `[lintegral_mul_const _ hKind, lintegral_indicator_one hKm]`. Conclude with `ENNReal.mul_lt_top hKc.measure_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hVpos))`.
-/
theorem lintegral_indicator_ne_top (μ : Measure G) [μ.IsHaarMeasure]
    (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] {C : Set G}
    (hT : IsClosed (T : Set G)) (hC : IsCompact C) {ρ0 : G → ℝ≥0∞}
    (h0 : IsQuotNormaliser T ν ρ0) :
    ∫⁻ g, ((T : Set G) * C).indicator 1 g * ρ0 g ∂μ ≠ ⊤ := by
  classical
  have : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set G)
  have : SigmaCompactSpace T := inferInstance
  have : SFinite ν := inferInstance
  have hmcoe : Measurable (fun h : T => (h : G)) := measurable_subtype_coe
  have : ν.IsMulRightInvariant := by
    have : ν.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at this
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  set K : Set G := U * C with hKdef
  have hKc : IsCompact K := hUc.mul hC
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  set S : Set G := (T : Set G) * C with hSdef
  have hSm : MeasurableSet S := (hT.mul_right_of_isCompact hC).measurableSet
  have hSinv : ∀ t ∈ T, ∀ x, t * x ∈ S ↔ x ∈ S := by
    intro t ht x
    constructor
    · rintro ⟨s, hs, c, hc, hsc⟩
      exact ⟨t⁻¹ * s, T.mul_mem (T.inv_mem ht) hs, c, hc, by
        show t⁻¹ * s * c = x
        rw [mul_assoc, show s * c = t * x from hsc, inv_mul_cancel_left]⟩
    · rintro ⟨s, hs, c, hc, rfl⟩
      exact ⟨t * s, T.mul_mem ht hs, c, hc, mul_assoc _ _ _⟩
  have hKind : Measurable (K.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hKm
  set I : G → ℝ≥0∞ := fun g => ∫⁻ h : T, K.indicator 1 ((h : G) * g) ∂ν with hIdef
  have hIm : Measurable I := by
    have : Measurable (fun p : G × T => K.indicator (1 : G → ℝ≥0∞) ((p.2 : G) * p.1)) :=
      hKind.comp ((hmcoe.comp measurable_snd).mul measurable_fst)
    exact this.lintegral_prod_right'
  have hIT : ∀ t ∈ T, ∀ g, I (t * g) = I g := by
    intro t ht g
    have := lintegral_mul_right_eq_self (μ := ν)
      (fun h : T => K.indicator (1 : G → ℝ≥0∞) ((h : G) * g)) ⟨t, ht⟩
    simp only [hIdef]
    rw [← this]
    refine lintegral_congr fun h => ?_
    simp [mul_assoc]
  set V : Set T := (fun h : T => (h : G)) ⁻¹' interior U with hVdef
  have hVm : MeasurableSet V := hmcoe measurableSet_interior
  have hVpos : ν V ≠ 0 := by
    have hVo : IsOpen V := isOpen_interior.preimage continuous_subtype_val
    have h1 : (1 : T) ∈ V := by
      show ((1 : T) : G) ∈ interior U
      simpa using mem_interior_iff_mem_nhds.mpr hU1
    exact (hVo.measure_pos ν ⟨1, h1⟩).ne'
  have hIC : ∀ g ∈ S, ν V ≤ I g := by
    rintro _ ⟨t, ht, c, hc, rfl⟩
    rw [hIT t ht c, ← lintegral_indicator_one hVm]
    refine lintegral_mono fun h => ?_
    by_cases hh : h ∈ V
    · have hK : (h : G) * c ∈ K := Set.mul_mem_mul (interior_subset hh) hc
      simp [hh, hK]
    · simp [Set.indicator_apply, hh]
  have hIfin : ∀ g, I g ≠ ⊤ := by
    intro g
    have hemb : Topology.IsClosedEmbedding (fun h : T => (h : G) * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal
    have hmeas : Measurable (fun h : T => (h : G) * g) := hmcoe.mul_const g
    have : I g = ν ((fun h : T => (h : G) * g) ⁻¹' K) := by
      rw [← lintegral_indicator_one (hmeas hKm)]
      rfl
    rw [this]
    exact ((hemb.isCompact_preimage hKc).measure_lt_top).ne
  set ρ : G → ℝ≥0∞ := S.piecewise (fun g => K.indicator 1 g * (I g)⁻¹) ρ0 with hρdef
  have hρ : IsQuotNormaliser T ν ρ := by
    refine ⟨Measurable.piecewise hSm (hKind.mul hIm.inv) h0.1, fun g => ?_⟩
    by_cases hg : g ∈ S
    · have hmem : ∀ h : T, (h : G) * g ∈ S := fun h => (hSinv _ h.2 g).2 hg
      calc ∫⁻ h : T, ρ ((h : G) * g) ∂ν = ∫⁻ h : T, K.indicator 1 ((h : G) * g) * (I g)⁻¹ ∂ν := by
            refine lintegral_congr fun h => ?_
            simp only [hρdef, Set.piecewise_eq_of_mem _ _ _ (hmem h), hIT _ h.2]
        _ = I g * (I g)⁻¹ := lintegral_mul_const _ (hKind.comp (hmcoe.mul_const g))
        _ = 1 := ENNReal.mul_inv_cancel
              (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hVpos) (hIC g hg))) (hIfin g)
    · have hmem : ∀ h : T, (h : G) * g ∉ S := fun h hh => hg ((hSinv _ h.2 g).1 hh)
      rw [← h0.2 g]
      refine lintegral_congr fun h => ?_
      simp only [hρdef, Set.piecewise_eq_of_notMem _ _ _ (hmem h)]
  have hF1 : Measurable (S.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hSm
  have hFinv : ∀ h ∈ T, ∀ g, S.indicator (1 : G → ℝ≥0∞) (h * g) = S.indicator 1 g := by
    intro h hh g
    simp only [Set.indicator_apply, hSinv h hh g, Pi.one_apply]
  rw [lintegral_normaliser_eq hF1 hFinv h0 hρ]
  refine ne_of_lt (lt_of_le_of_lt (b := ∫⁻ g, K.indicator 1 g * (ν V)⁻¹ ∂μ)
    (lintegral_mono fun g => ?_) ?_)
  · by_cases hg : g ∈ S
    · simp only [Set.indicator_of_mem hg, Pi.one_apply, one_mul, hρdef,
        Set.piecewise_eq_of_mem _ _ _ hg]
      gcongr
      exact hIC g hg
    · simp [hg]
  · rw [lintegral_mul_const _ hKind, lintegral_indicator_one hKm]
    exact ENNReal.mul_lt_top hKc.measure_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hVpos))

/- English proof (translation)
Distinguish the cases in `hex : ∃ ρ, IsQuotNormaliser T ν ρ`. Establish `h0 : IsQuotNormaliser T ν hex.choose` using `hex.choose_spec set S : Set G := (T : Set G) * C with hSdef`. Establish `hL : ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤` using `lintegral_indicator_ne_top μ T ν hT hC h0`. Use `⟨(∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal, ENNReal.toReal_nonneg, fun F B hB hF hFT hFS hFC => ?_⟩` and prove the remaining obligations. Establish `hbound : ∀ g, ‖F g‖ₑ ≤ ENNReal.ofReal B * S.indicator 1 g`.

Introduce `g`. Distinguish the cases in `hg : g ∈ S`. Rewrite using `[Set.indicator_of_mem hg, Pi.one_apply, mul_one]`. Take `⟨t, ht, c, hc, rfl⟩` from `hg`. Rewrite using `[hFT t ht c, ← ofReal_norm]`.

Conclude with `ENNReal.ofReal_le_ofReal (hFC c hc)`. Establish `: F g = 0`. Assume the negation of the conclusion as `h`. Conclude with `hg (hFS g h)`. Simplify using `[this]`.

Establish `hle : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≤ ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc]`. Use `gcongr`. Conclude with `hbound g`.

Use `_ = ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Establish `hne : ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL`. Establish `hfin : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≠ ⊤` using `ne_top_of_le_ne_top hne hle`. Use `⟨by rw [quotLIntegral, dif_pos hex]; exact hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[quotIntegral, dif_pos hex]`.

Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.toReal_mono hfin ((enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun g => ?_))` and prove the remaining obligations. Rewrite using `[enorm_mul]`. Use `gcongr`. Conclude with `enorm_ofReal_toReal_le _`.

Use `_ ≤ (ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal := ENNReal.toReal_mono hne hle`. Use `_ = (∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal * B := by`. Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, mul_comm]`. Use `⟨0, le_rfl, fun F B _ _ _ _ _ => ?_⟩` and prove the remaining obligations. Simplify using `[quotLIntegral, quotIntegral, hex]`.
-/
theorem main (μ : Measure G) [μ.IsHaarMeasure] (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] (C : Set G) (hT : IsClosed (T : Set G)) (hC : IsCompact C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (F : G → ℂ) (B : ℝ), 0 ≤ B → Measurable F →
      (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ x, F x ≠ 0 → x ∈ (T : Set G) * C) →
      (∀ x ∈ C, ‖F x‖ ≤ B) → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ ∧
        ‖quotIntegral μ T ν F‖ ≤ A * B := by
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  · have h0 : IsQuotNormaliser T ν hex.choose := hex.choose_spec
    set S : Set G := (T : Set G) * C with hSdef
    have hL : ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤ :=
      lintegral_indicator_ne_top μ T ν hT hC h0
    refine ⟨(∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal, ENNReal.toReal_nonneg,
      fun F B hB hF hFT hFS hFC => ?_⟩
    have hbound : ∀ g, ‖F g‖ₑ ≤ ENNReal.ofReal B * S.indicator 1 g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, Pi.one_apply, mul_one]
        obtain ⟨t, ht, c, hc, rfl⟩ := hg
        rw [hFT t ht c, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hFC c hc)
      · have : F g = 0 := by
          by_contra h
          exact hg (hFS g h)
        simp [this]
    have hle : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≤
        ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ := by
      calc ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ
          ≤ ∫⁻ g, ENNReal.ofReal B * (S.indicator 1 g * hex.choose g) ∂μ :=
            lintegral_mono fun g => by
              rw [← mul_assoc]
              gcongr
              exact hbound g
        _ = ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hne : ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL
    have hfin : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≠ ⊤ := ne_top_of_le_ne_top hne hle
    refine ⟨by rw [quotLIntegral, dif_pos hex]; exact hfin, ?_⟩
    rw [quotIntegral, dif_pos hex]
    calc ‖∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ‖
        = ‖∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ‖ₑ.toReal := (toReal_enorm _).symm
      _ ≤ (∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ).toReal := by
          refine ENNReal.toReal_mono hfin ((enorm_integral_le_lintegral_enorm _).trans
            (lintegral_mono fun g => ?_))
          rw [enorm_mul]
          gcongr
          exact enorm_ofReal_toReal_le _
      _ ≤ (ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal :=
          ENNReal.toReal_mono hne hle
      _ = (∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal * B := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, mul_comm]
  · refine ⟨0, le_rfl, fun F B _ _ _ _ _ => ?_⟩
    simp [quotLIntegral, quotIntegral, hex]

end QuotientIntegral

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ T ν _ _ C hT hC`. Conclude with `QuotientIntegral.main μ T ν C hT hC`.
-/
theorem pf_QInt : QInt := by
  intro G _ _ _ _ _ _ _ _ μ _ T ν _ _ C hT hC
  exact QuotientIntegral.main μ T ν C hT hC

end PositivityTheory.Rg.BcB.CV
