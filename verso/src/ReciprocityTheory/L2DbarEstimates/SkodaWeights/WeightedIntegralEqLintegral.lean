import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaWeightStatement

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

/- English proof (translation)
The claim follows from `(hψ.neg.exp).ennreal_ofReal`.
-/
lemma measurable_exp_neg_density {M : Type*} [MeasurableSpace M] {ψ : M → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (-ψ x))) := (hψ.neg.exp).ennreal_ofReal

/- English proof (translation)
Unfold `wvol`. Rewrite using `[ae_withDensity_iff (measurable_exp_neg_density hψ)]`. Use `⟨fun h => h.mono fun x hx => hx ?_, fun h => h.mono fun x hx _ => hx⟩` and prove the remaining obligations. Conclude with `(ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'`.
-/
lemma ae_weighted_iff_ae (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (P : M → Prop) :
    (∀ᵐ x ∂wvol n z ψ, P x) ↔ ∀ᵐ x ∂vol n z, P x := by
  unfold wvol
  rw [ae_withDensity_iff (measurable_exp_neg_density hψ)]
  refine ⟨fun h => h.mono fun x hx => hx ?_, fun h => h.mono fun x hx _ => hx⟩
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/- English proof (translation)
Unfold `wint wvol`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_exp_neg_density hψ) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`. Rewrite using `[mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.rpow_two, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]`.
-/
lemma weightedIntegral_eq_lintegral (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    wint n z f ψ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂wvol n z ψ := by
  unfold wint wvol
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_exp_neg_density hψ)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.rpow_two,
    ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

/- English proof (translation)
Rewrite using `[eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ENNReal.toReal_ofNat, ← weightedIntegral_eq_lintegral n z hψ f]`.
-/
lemma eLpNorm_two_weighted_eq (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) {ψ : M → ℝ}
    (hψ : Measurable ψ) (f : M → ℂ) :
    eLpNorm f 2 (wvol n z ψ) = wint n z f ψ ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
    ← weightedIntegral_eq_lintegral n z hψ f]

/- English proof (translation)
Introduce `z ψ hψ`. Use `⟨fun P => ae_weighted_iff_ae n z hψ P, fun F => ?_, fun f hf hfin => ?_⟩` and prove the remaining obligations. Establish `hlt` using `Lp.eLpNorm_lt_top F`. Establish `hw : wint n z F ψ = eLpNorm F 2 (wvol n z ψ) ^ (2 : ℝ)`. Rewrite using `[eLpNorm_two_weighted_eq n z hψ, ← ENNReal.rpow_mul]`.

Evaluate the numerical expressions. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`. Conclude with `ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne`. Rewrite using `[hw, Lp.norm_def, ← ENNReal.toReal_rpow, Real.rpow_two]`.

Establish `hmem : MemLp f 2 (wvol n z ψ)`. Use `⟨hf.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[eLpNorm_two_weighted_eq n z hψ f]`. Conclude with `ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne`. Conclude with `⟨hmem.toLp f, (ae_weighted_iff_ae n z hψ (fun x => (hmem.toLp f : M → ℂ) x = f x)).mp (MemLp.coeFn_toLp hmem)⟩`.
-/
theorem l2w (n : ℕ) (M : Type*) [MeasurableSpace M] : WeightedL2Properties n M := by
  intro z ψ hψ
  refine ⟨fun P => ae_weighted_iff_ae n z hψ P, fun F => ?_, fun f hf hfin => ?_⟩
  · have hlt := Lp.eLpNorm_lt_top F
    have hw : wint n z F ψ = eLpNorm F 2 (wvol n z ψ) ^ (2 : ℝ) := by
      rw [eLpNorm_two_weighted_eq n z hψ, ← ENNReal.rpow_mul]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [hw]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne
    · rw [hw, Lp.norm_def, ← ENNReal.toReal_rpow, Real.rpow_two]
  · have hmem : MemLp f 2 (wvol n z ψ) := by
      refine ⟨hf.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
      rw [eLpNorm_two_weighted_eq n z hψ f]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
    exact ⟨hmem.toLp f, (ae_weighted_iff_ae n z hψ (fun x => (hmem.toLp f : M → ℂ) x = f x)).mp
      (MemLp.coeFn_toLp hmem)⟩

/- English proof (translation)
Introduce `z hz U hU ⟨x, hx⟩`. Take `⟨e, he, hxe⟩` from `exists_chart n z hz x`. Establish `hW : IsOpen (U ∩ e.source)` using `hU.inter e.open_source`. Establish `hinj : Set.InjOn z e.source`. Introduce `a ha b hb hab`.

Rewrite `hab` using `[he ha, he hb]`. Conclude with `e.injOn ha hb hab`. Establish `himg : z '' (U ∩ e.source) = e '' (U ∩ e.source)` using `Set.image_congr fun y hy => he hy.2`. Establish `hpos : 0 < volume (z '' (U ∩ e.source))`. Rewrite using `[himg]`.

Conclude with `(e.isOpen_image_of_subset_source hW Set.inter_subset_right).measure_pos _ ⟨e x, x, ⟨hx, hxe⟩, rfl⟩`. Rewrite `hpos` using `[← vol_image n z hz e.source e.open_source hinj _ hW.measurableSet Set.inter_subset_right]`. Conclude with `hpos.trans_le (measure_mono Set.inter_subset_left)`.
-/
theorem volOpenPos (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    VolOpenPosStatement n M := by
  intro z hz U hU ⟨x, hx⟩
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  have hW : IsOpen (U ∩ e.source) := hU.inter e.open_source
  have hinj : Set.InjOn z e.source := by
    intro a ha b hb hab
    rw [he ha, he hb] at hab
    exact e.injOn ha hb hab
  have himg : z '' (U ∩ e.source) = e '' (U ∩ e.source) :=
    Set.image_congr fun y hy => he hy.2
  have hpos : 0 < volume (z '' (U ∩ e.source)) := by
    rw [himg]
    exact (e.isOpen_image_of_subset_source hW Set.inter_subset_right).measure_pos _
      ⟨e x, x, ⟨hx, hxe⟩, rfl⟩
  rw [← vol_image n z hz e.source e.open_source hinj _ hW.measurableSet
    Set.inter_subset_right] at hpos
  exact hpos.trans_le (measure_mono Set.inter_subset_left)

end ReciprocityTheory.L2DbarEstimates.H
