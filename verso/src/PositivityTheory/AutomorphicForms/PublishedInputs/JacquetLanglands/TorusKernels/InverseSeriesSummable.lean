import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UpperTheory.Esk.InverseSeriesLemmas

/- English proof (translation)
Rewrite using `[enorm_smul, Real.enorm_eq_ofReal hr]`.
-/
theorem enorm_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (x : ℂ) : ‖r • x‖ₑ = ENNReal.ofReal r * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal hr]

/- English proof (translation)
Establish `h` using `(Equiv.inv G).hasSum_iff.mpr (hb.sum y)`. Conclude with `h`.
-/
theorem hasSum_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : HasSum (fun g : G => b (g⁻¹ • y)) 1 := by
  have h := (Equiv.inv G).hasSum_iff.mpr (hb.sum y)
  exact h

/- English proof (translation)
Establish `hs` using `UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb y`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tsum_ofReal_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
  have hs := UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb y
  calc ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ENNReal.ofReal (∑' g : G, b (g⁻¹ • y)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) hs.summable).symm
    _ = 1 := by rw [hs.tsum_eq, ENNReal.ofReal_one]

end UpperTheory.Esk.InverseSeriesLemmas

open UpperTheory.Esk.InverseSeriesLemmas in
/- English proof (translation)
Unfold `UpperTheory.Esk.C3`. Introduce `G Y _ _ _ _ μ hμ b hb f hf hfi`. Establish `hμ' : ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ` using `hμ`. Take `⟨Φ, hΦ⟩ : ∃ Φ : G → Y → ℂ, ∀ g y, Φ g y = b y • f (g • y)` from `⟨_, fun _ _ => rfl⟩`. Take `⟨Ψ, hΨ⟩ : ∃ Ψ : G → Y → ℂ, ∀ g y, Ψ g y = b (g⁻¹ • y) • f y` from `⟨_, fun _ _ => rfl⟩`.

Establish `hΦm : ∀ g, Measurable (Φ g)`. Introduce `g`. Rewrite using `[show Φ g = fun y => b y • f (g • y) from funext (hΦ g)]`. Conclude with `hb.meas.smul (hf.comp (hμ' g).measurable)`. Establish `hΨm : ∀ g, Measurable (Ψ g)`.

Introduce `g`. Rewrite using `[show Ψ g = fun y => b (g⁻¹ • y) • f y from funext (hΨ g)]`. Conclude with `(hb.meas.comp (hμ' g⁻¹).measurable).smul hf`. Establish `emb : ∀ g : G, MeasurableEmbedding (fun y : Y => g • y)` using `fun g => (MeasurableEquiv.mk (MulAction.toPerm g) (hμ' g).measurable (hμ' g⁻¹).measurable).measurableEmbedding`. Establish `hΨl : ∀ g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ` using `fun g => lintegral_congr (fun z => by rw [hΨ, UpperTheory.Esk.InverseSeriesLemmas.enorm_smul_nonneg _ (hb.nonneg _)])`.

Establish `hΦl : ∀ g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖Ψ g z‖ₑ ∂μ`. Introduce `g`. Rewrite using `[← (hμ' g).lintegral_comp (hΨm g).enorm]`. Conclude with `lintegral_congr (fun y => by rw [hΦ, hΨ, inv_smul_smul])`. Establish `hfin : ∫⁻ z, ‖f z‖ₑ ∂μ < ⊤` using `hfi.2`.

Establish `hsumΨ : ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.tsum_mul_right, UpperTheory.Esk.InverseSeriesLemmas.tsum_ofReal_inv b hb z, one_mul])`. Establish `hsumΦ' : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ` using `(tsum_congr hΦl).trans hsumΨ`. Establish `hsumΦ : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ ≠ ⊤` using `by rw [hsumΦ']; exact hfin.ne`.

Establish `hΦi : ∀ g, ∫ y, Φ g y ∂μ = ∫ z, Ψ g z ∂μ`. Introduce `g`. Rewrite using `[← (hμ' g).integral_comp (emb g) (Ψ g)]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Rewrite using `[hΦ, hΨ, inv_smul_smul]`. Establish `hΨt : ∫ z, ∑' g, Ψ g z ∂μ = ∑' g, ∫ z, Ψ g z ∂μ` using `integral_tsum (fun g => (hΨm g).aestronglyMeasurable) (by rw [hsumΨ]; exact hfin.ne)`. Establish `hΨp : ∀ z, ∑' g, Ψ g z = f z`. Introduce `z`. Simplify using `only [hΨ]`.

Rewrite using `[((UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb z).smul_const (f z)).tsum_eq, one_smul]`. Establish `hΦt : ∫ y, ∑' g, Φ g y ∂μ = ∑' g, ∫ y, Φ g y ∂μ` using `integral_tsum (fun g => (hΦm g).aestronglyMeasurable) hsumΦ`. Establish `hΦp : ∀ y, ∑' g, Φ g y = b y • ∑' g : G, f (g • y)`. Introduce `y`. Simplify using `only [hΦ]`.

Conclude with `tsum_const_smul'' (b y)`. Establish `hfun : (fun y => b y • ∑' g : G, f (g • y)) = fun y => ∑' g, Φ g y`. Use function extensionality and compare the values at `(fun y => (hΦp y).symm)`. Establish `heq : ∫ y, b y • ∑' g : G, f (g • y) ∂μ = ∫ y, f y ∂μ`. Rewrite using `[hfun, hΦt, tsum_congr hΦi, ← hΨt]`.

Use `congr 1`. Use function extensionality and compare the values at `z`. Conclude with `hΨp z`. Establish `hint : Integrable (fun y => ∑' g, Φ g y) μ`. Use `⟨AEStronglyMeasurable.tsum (fun g => (hΦm g).aestronglyMeasurable), ?_⟩` and prove the remaining obligations.

Establish `hle : ∫⁻ y, ‖∑' g, Φ g y‖ₑ ∂μ ≤ ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ` using `lintegral_mono (fun y => enorm_tsum_le_tsum_enorm)`. Establish `hsum_eq : ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ = ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ` using `lintegral_tsum (fun g => (hΦm g).enorm.aemeasurable)`. Conclude with `lt_of_le_of_lt (hle.trans hsum_eq.le) (lt_top_iff_ne_top.mpr hsumΦ)`. Conclude with `⟨by rw [hfun]; exact hint, heq⟩`.
-/
theorem UpperTheory.Esk.inverse_series_summable : UpperTheory.Esk.C3 := by
  unfold UpperTheory.Esk.C3
  intro G Y _ _ _ _ μ hμ b hb f hf hfi
  have hμ' : ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ := hμ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → Y → ℂ, ∀ g y, Φ g y = b y • f (g • y) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : G → Y → ℂ, ∀ g y, Ψ g y = b (g⁻¹ • y) • f y := ⟨_, fun _ _ => rfl⟩
  have hΦm : ∀ g, Measurable (Φ g) := by
    intro g
    rw [show Φ g = fun y => b y • f (g • y) from funext (hΦ g)]
    exact hb.meas.smul (hf.comp (hμ' g).measurable)
  have hΨm : ∀ g, Measurable (Ψ g) := by
    intro g
    rw [show Ψ g = fun y => b (g⁻¹ • y) • f y from funext (hΨ g)]
    exact (hb.meas.comp (hμ' g⁻¹).measurable).smul hf
  have emb : ∀ g : G, MeasurableEmbedding (fun y : Y => g • y) := fun g =>
    (MeasurableEquiv.mk (MulAction.toPerm g) (hμ' g).measurable (hμ' g⁻¹).measurable).measurableEmbedding
  have hΨl : ∀ g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ := fun g =>
    lintegral_congr (fun z => by rw [hΨ, UpperTheory.Esk.InverseSeriesLemmas.enorm_smul_nonneg _ (hb.nonneg _)])
  have hΦl : ∀ g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖Ψ g z‖ₑ ∂μ := by
    intro g
    rw [← (hμ' g).lintegral_comp (hΨm g).enorm]
    exact lintegral_congr (fun y => by rw [hΦ, hΨ, inv_smul_smul])
  have hfin : ∫⁻ z, ‖f z‖ₑ ∂μ < ⊤ := hfi.2
  have hsumΨ : ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := by
    calc ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∑' g : G, ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          tsum_congr hΨl
      _ = ∫⁻ z, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          (lintegral_tsum (fun g =>
            ((hb.meas.comp (hμ' g⁻¹).measurable).ennreal_ofReal.mul hf.enorm).aemeasurable)).symm
      _ = ∫⁻ z, ‖f z‖ₑ ∂μ := lintegral_congr (fun z => by
          rw [ENNReal.tsum_mul_right, UpperTheory.Esk.InverseSeriesLemmas.tsum_ofReal_inv b hb z, one_mul])
  have hsumΦ' : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := (tsum_congr hΦl).trans hsumΨ
  have hsumΦ : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ ≠ ⊤ := by rw [hsumΦ']; exact hfin.ne
  have hΦi : ∀ g, ∫ y, Φ g y ∂μ = ∫ z, Ψ g z ∂μ := by
    intro g
    rw [← (hμ' g).integral_comp (emb g) (Ψ g)]
    congr 1
    funext y
    rw [hΦ, hΨ, inv_smul_smul]
  have hΨt : ∫ z, ∑' g, Ψ g z ∂μ = ∑' g, ∫ z, Ψ g z ∂μ :=
    integral_tsum (fun g => (hΨm g).aestronglyMeasurable) (by rw [hsumΨ]; exact hfin.ne)
  have hΨp : ∀ z, ∑' g, Ψ g z = f z := by
    intro z
    simp only [hΨ]
    rw [((UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb z).smul_const (f z)).tsum_eq, one_smul]
  have hΦt : ∫ y, ∑' g, Φ g y ∂μ = ∑' g, ∫ y, Φ g y ∂μ :=
    integral_tsum (fun g => (hΦm g).aestronglyMeasurable) hsumΦ
  have hΦp : ∀ y, ∑' g, Φ g y = b y • ∑' g : G, f (g • y) := by
    intro y
    simp only [hΦ]
    exact tsum_const_smul'' (b y)
  have hfun : (fun y => b y • ∑' g : G, f (g • y)) = fun y => ∑' g, Φ g y :=
    funext (fun y => (hΦp y).symm)
  have heq : ∫ y, b y • ∑' g : G, f (g • y) ∂μ = ∫ y, f y ∂μ := by
    rw [hfun, hΦt, tsum_congr hΦi, ← hΨt]
    congr 1
    funext z
    exact hΨp z
  have hint : Integrable (fun y => ∑' g, Φ g y) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun g => (hΦm g).aestronglyMeasurable), ?_⟩
    have hle : ∫⁻ y, ‖∑' g, Φ g y‖ₑ ∂μ ≤ ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ :=
      lintegral_mono (fun y => enorm_tsum_le_tsum_enorm)
    have hsum_eq : ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ = ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ :=
      lintegral_tsum (fun g => (hΦm g).enorm.aemeasurable)
    exact lt_of_le_of_lt (hle.trans hsum_eq.le) (lt_top_iff_ne_top.mpr hsumΦ)
  exact ⟨by rw [hfun]; exact hint, heq⟩
