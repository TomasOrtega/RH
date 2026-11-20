import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

namespace GlobalTheory.ChartSumBound

/- English proof (translation)
Use `set cj := B.chart j with hcj`. Use `set ck := B.chart k with hck`. Use `set O := ck.target ∩ ck.symm ⁻¹' cj.source with hOdef`. Use `set O' := cj.target ∩ cj.symm ⁻¹' ck.source with hO'def`. Establish `hO : IsOpen O` using `ck.continuousOn_symm.isOpen_inter_preimage ck.open_target cj.open_source`.

Establish `hO' : IsOpen O'` using `cj.continuousOn_symm.isOpen_inter_preimage cj.open_target ck.open_source`. Establish `hτ : AnalyticOnNhd ℂ (cj ∘ ck.symm) O` using `B.holo k j`. Establish `hinj : Set.InjOn (cj ∘ ck.symm) O`. Introduce `a ha b hb hab`. Conclude with `ck.symm.injOn ha.1 hb.1 (cj.injOn ha.2 hb.2 hab)`.

Establish `himg : (cj ∘ ck.symm) '' O = O'`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Use `⟨cj.map_source hz.2, ?_⟩` and prove the remaining obligations.

Use `show cj.symm (cj (ck.symm z)) ∈ ck.source`. Rewrite using `[cj.left_inv hz.2]`. Conclude with `ck.map_target hz.1`. Introduce and unpack `⟨hw, h2⟩`. Use `⟨ck (cj.symm w), ⟨ck.map_source h2, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show ck.symm (ck (cj.symm w)) ∈ cj.source`. Rewrite using `[ck.left_inv h2]`. Conclude with `cj.map_target hw`. Use `show cj (ck.symm (ck (cj.symm w))) = w`. Rewrite using `[ck.left_inv h2, cj.right_inv hw]`.

Use `set F : (Fin n → ℂ) → ℝ≥0∞ := fun w => ENNReal.ofReal (χ (cj.symm w)) * (g (cj.symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ) with hF`. Establish `h1 : ∫⁻ w in cj.target, F w = ∫⁻ w in cj.target, O'.indicator F w`. Use `setLIntegral_congr_fun cj.open_target.measurableSet fun w hw => ?_` and prove the remaining obligations. Distinguish the cases in `hwO : w ∈ O'`. Rewrite using `[Set.indicator_of_mem hwO]`.

Rewrite using `[Set.indicator_of_notMem hwO]`. Establish `: cj.symm w ∉ ck.source` using `fun h => hwO ⟨hw, h⟩`. Simplify using `[hF, hsupp _ this]`. Establish `h2 : ∫⁻ w in cj.target, O'.indicator F w ≤ ∫⁻ w in O', F w`. Rewrite using `[setLIntegral_indicator hO'.measurableSet]`.

Conclude with `lintegral_mono_set Set.inter_subset_left`. Establish `h3 : ∫⁻ w in O', F w = ∫⁻ z in O, ENNReal.ofReal (χ (ck.symm z)) * (g (ck.symm z) * ‖locDens B (fun _ => Ψ) k z‖ₑ)`. Rewrite using `[← himg, ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul _ _ hO hτ hinj]`. Use `setLIntegral_congr_fun hO.measurableSet fun z hz => ?_` and prove the remaining obligations. Establish `hz2 : ck.symm z ∈ cj.source` using `hz.2`.

Establish `hl` using `locDensChart B (fun _ => Ψ) (fun _ => hΨ) k j z hz.1 hz2`. Establish `hs : cj.symm ((cj ∘ ck.symm) z) = ck.symm z`. Simplify using `only [Function.comp_apply]`. Conclude with `cj.left_inv hz2`. Simplify using `only [hF, hs]`.

Rewrite using `[ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hl, enorm_mul, Real.enorm_eq_ofReal (sq_nonneg _)]`. Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem move_le {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (B : FinHolAtlas n Y) (Ψ : LocPot Y) (hΨ : IsPotential B Ψ) (χ : Y → ℝ)
    (k j : Fin B.n) (hsupp : ∀ y, y ∉ (B.chart k).source → χ y = 0) (g : Y → ℝ≥0∞) :
    ∫⁻ w in (B.chart j).target, ENNReal.ofReal (χ ((B.chart j).symm w)) *
        (g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ) ≤
      ∫⁻ z in (B.chart k).target, ENNReal.ofReal (χ ((B.chart k).symm z)) *
        (g ((B.chart k).symm z) * ‖locDens B (fun _ => Ψ) k z‖ₑ) := by
  set cj := B.chart j with hcj
  set ck := B.chart k with hck
  set O := ck.target ∩ ck.symm ⁻¹' cj.source with hOdef
  set O' := cj.target ∩ cj.symm ⁻¹' ck.source with hO'def
  have hO : IsOpen O := ck.continuousOn_symm.isOpen_inter_preimage ck.open_target cj.open_source
  have hO' : IsOpen O' := cj.continuousOn_symm.isOpen_inter_preimage cj.open_target ck.open_source
  have hτ : AnalyticOnNhd ℂ (cj ∘ ck.symm) O := B.holo k j
  have hinj : Set.InjOn (cj ∘ ck.symm) O := by
    intro a ha b hb hab
    exact ck.symm.injOn ha.1 hb.1 (cj.injOn ha.2 hb.2 hab)
  have himg : (cj ∘ ck.symm) '' O = O' := by
    ext w; constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨cj.map_source hz.2, ?_⟩
      show cj.symm (cj (ck.symm z)) ∈ ck.source
      rw [cj.left_inv hz.2]; exact ck.map_target hz.1
    · rintro ⟨hw, h2⟩
      refine ⟨ck (cj.symm w), ⟨ck.map_source h2, ?_⟩, ?_⟩
      · show ck.symm (ck (cj.symm w)) ∈ cj.source
        rw [ck.left_inv h2]; exact cj.map_target hw
      · show cj (ck.symm (ck (cj.symm w))) = w
        rw [ck.left_inv h2, cj.right_inv hw]
  set F : (Fin n → ℂ) → ℝ≥0∞ := fun w => ENNReal.ofReal (χ (cj.symm w)) *
        (g (cj.symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ) with hF
  have h1 : ∫⁻ w in cj.target, F w = ∫⁻ w in cj.target, O'.indicator F w := by
    refine setLIntegral_congr_fun cj.open_target.measurableSet fun w hw => ?_
    by_cases hwO : w ∈ O'
    · rw [Set.indicator_of_mem hwO]
    · rw [Set.indicator_of_notMem hwO]
      have : cj.symm w ∉ ck.source := fun h => hwO ⟨hw, h⟩
      simp [hF, hsupp _ this]
  have h2 : ∫⁻ w in cj.target, O'.indicator F w ≤ ∫⁻ w in O', F w := by
    rw [setLIntegral_indicator hO'.measurableSet]
    exact lintegral_mono_set Set.inter_subset_left
  have h3 : ∫⁻ w in O', F w = ∫⁻ z in O, ENNReal.ofReal (χ (ck.symm z)) *
        (g (ck.symm z) * ‖locDens B (fun _ => Ψ) k z‖ₑ) := by
    rw [← himg, ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul _ _ hO hτ hinj]
    refine setLIntegral_congr_fun hO.measurableSet fun z hz => ?_
    have hz2 : ck.symm z ∈ cj.source := hz.2
    have hl := locDensChart B (fun _ => Ψ) (fun _ => hΨ) k j z hz.1 hz2
    have hs : cj.symm ((cj ∘ ck.symm) z) = ck.symm z := by
      simp only [Function.comp_apply]; exact cj.left_inv hz2
    simp only [hF, hs]
    rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hl, enorm_mul,
      Real.enorm_eq_ofReal (sq_nonneg _)]
    simp only [Function.comp_apply]
    ring
  calc ∫⁻ w in cj.target, F w ≤ ∫⁻ w in O', F w := h1 ▸ h2
    _ = _ := h3
    _ ≤ _ := lintegral_mono_set Set.inter_subset_left

/- English proof (translation)
Rewrite using `[maMeasure_eq_sum B _ hne, lintegral_finsetSum_measure]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Unfold `chartMeasure`. Establish `hTm` using `(B.chart k).open_target.measurableSet`. Establish `hsm : AEMeasurable (B.chart k).symm (volume.restrict (B.chart k).target)` using `(B.chart k).continuousOn_symm.aemeasurable hTm`.

Establish `hχc : ContinuousOn (fun y => hne.some.χ k ((B.chart k).symm y)) (B.chart k).target`. Simplify `(hne.some.smooth k k).continuousOn` using `[Function.comp_def]`. Establish `hdc` using `locDensCont B (fun _ => Ψ) (fun _ => hΨ) k`. Rewrite using `[lintegral_map' hg.aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)), lintegral_withDensity_eq_lintegral_mul₀ (f := fun y => ENNReal.ofReal (hne.some.χ k ((B.chart k).symm y) * locDens B (fun _ => Ψ) k y)) (g := fun a => g ((B.chart k).symm a)) ((hχc.mul hdc).aeme …`. Use `setLIntegral_congr_fun hTm fun z hz => ?_` and prove the remaining obligations.

Establish `h0` using `locDens_nonneg_of_psh B (fun _ => Ψ) (fun _ => hΨ) (fun _ => hpsh) k hz`. Simplify using `only [Pi.mul_apply, Function.comp_apply]`. Rewrite using `[ENNReal.ofReal_mul (hne.some.nonneg k _), Real.enorm_eq_ofReal h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_maMeasure_eq {n : ℕ} {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (B : FinHolAtlas n Y) (Ψ : LocPot Y) (hΨ : IsPotential B Ψ) (hpsh : IsPsh B Ψ)
    (hne : Nonempty (ChartPartition B)) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂maMeasure B (fun _ => Ψ) = ∑ k, ∫⁻ z in (B.chart k).target,
      ENNReal.ofReal (hne.some.χ k ((B.chart k).symm z)) *
        (g ((B.chart k).symm z) * ‖locDens B (fun _ => Ψ) k z‖ₑ) := by
  rw [maMeasure_eq_sum B _ hne, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold chartMeasure
  have hTm := (B.chart k).open_target.measurableSet
  have hsm : AEMeasurable (B.chart k).symm (volume.restrict (B.chart k).target) :=
    (B.chart k).continuousOn_symm.aemeasurable hTm
  have hχc : ContinuousOn (fun y => hne.some.χ k ((B.chart k).symm y)) (B.chart k).target := by
    simpa [Function.comp_def] using (hne.some.smooth k k).continuousOn
  have hdc := locDensCont B (fun _ => Ψ) (fun _ => hΨ) k
  rw [lintegral_map' hg.aemeasurable (hsm.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul₀
      (f := fun y => ENNReal.ofReal (hne.some.χ k ((B.chart k).symm y) * locDens B (fun _ => Ψ) k y))
      (g := fun a => g ((B.chart k).symm a))
      ((hχc.mul hdc).aemeasurable hTm).ennreal_ofReal (hg.comp_aemeasurable hsm)]
  refine setLIntegral_congr_fun hTm fun z hz => ?_
  have h0 := locDens_nonneg_of_psh B (fun _ => Ψ) (fun _ => hΨ) (fun _ => hpsh) k hz
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [ENNReal.ofReal_mul (hne.some.nonneg k _), Real.enorm_eq_ofReal h0]
  ring

/- English proof (translation)
Introduce `n Y _ _ _ _ _ B Ψ hΨ hpsh U g hg`. Establish `hne : Nonempty (ChartPartition B)` using `existsPartition B`. Rewrite using `[lintegral_maMeasure_eq B Ψ hΨ hpsh hne g hg]`. Establish `hj : ∀ j, ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' U, g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ ≤ ∑ k, ∫⁻ z in (B.chart k).target, ENNReal.ofReal (hne.some.χ k ((B.chart k).symm z)) * (g ((B.chart k).symm z) * ‖locDens B (fun _ => Ψ) k z‖ₑ)`. Introduce `j`.

Establish `hTm` using `(B.chart j).open_target.measurableSet`. Establish `hsm : AEMeasurable (B.chart j).symm (volume.restrict (B.chart j).target)` using `(B.chart j).continuousOn_symm.aemeasurable hTm`. Establish `hdc` using `locDensCont B (fun _ => Ψ) (fun _ => hΨ) j`. Establish `hmeas : ∀ k ∈ Finset.univ, AEMeasurable (fun w => ENNReal.ofReal (hne.some.χ k ((B.chart j).symm w)) * (g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ)) (volume.restrict (B.chart j).target)`. Introduce `k _`.

Establish `hχc : ContinuousOn (fun y => hne.some.χ k ((B.chart j).symm y)) (B.chart j).target`. Simplify `(hne.some.smooth k j).continuousOn` using `[Function.comp_def]`. Conclude with `(hχc.aemeasurable hTm).ennreal_ofReal.mul ((hg.comp_aemeasurable hsm).mul (hdc.aemeasurable hTm).enorm)`. Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_congr_fun hTm fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hne.some.nonneg k _), hne.some.sum_eq_one, ENNReal.ofReal_one, one_mul]`. Use `_ = ∑ k, ∫⁻ w in (B.chart j).target, ENNReal.ofReal (hne.some.χ k ((B.chart j).symm w)) * (g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ) := lintegral_finsetSum' _ hmeas`. Use `_ ≤ _ := Finset.sum_le_sum fun k _ => move_le B Ψ hΨ _ k j (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hne.some.tsupport_subset k h))) g`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem chartSumInt_le_card_mul :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
      [BorelSpace Y] (B : FinHolAtlas n Y) (Ψ : LocPot Y), IsPotential B Ψ → IsPsh B Ψ →
      ∀ (U : Set Y) (g : Y → ℝ≥0∞), Measurable g →
        chartSumInt B Ψ U g ≤ (B.n : ℝ≥0∞) * ∫⁻ y, g y ∂maMeasure B (fun _ => Ψ) := by
  intro n Y _ _ _ _ _ B Ψ hΨ hpsh U g hg
  have hne : Nonempty (ChartPartition B) := existsPartition B
  rw [lintegral_maMeasure_eq B Ψ hΨ hpsh hne g hg]
  have hj : ∀ j, ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
      g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ ≤
      ∑ k, ∫⁻ z in (B.chart k).target,
        ENNReal.ofReal (hne.some.χ k ((B.chart k).symm z)) *
          (g ((B.chart k).symm z) * ‖locDens B (fun _ => Ψ) k z‖ₑ) := by
    intro j
    have hTm := (B.chart j).open_target.measurableSet
    have hsm : AEMeasurable (B.chart j).symm (volume.restrict (B.chart j).target) :=
      (B.chart j).continuousOn_symm.aemeasurable hTm
    have hdc := locDensCont B (fun _ => Ψ) (fun _ => hΨ) j
    have hmeas : ∀ k ∈ Finset.univ, AEMeasurable (fun w => ENNReal.ofReal
        (hne.some.χ k ((B.chart j).symm w)) *
        (g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ))
        (volume.restrict (B.chart j).target) := by
      intro k _
      have hχc : ContinuousOn (fun y => hne.some.χ k ((B.chart j).symm y)) (B.chart j).target := by
        simpa [Function.comp_def] using (hne.some.smooth k j).continuousOn
      exact (hχc.aemeasurable hTm).ennreal_ofReal.mul
        ((hg.comp_aemeasurable hsm).mul (hdc.aemeasurable hTm).enorm)
    calc _ ≤ ∫⁻ w in (B.chart j).target,
          g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ :=
          lintegral_mono_set Set.inter_subset_left
      _ = ∫⁻ w in (B.chart j).target, ∑ k, ENNReal.ofReal
          (hne.some.χ k ((B.chart j).symm w)) *
            (g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ) := by
          refine setLIntegral_congr_fun hTm fun w _ => ?_
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hne.some.nonneg k _),
            hne.some.sum_eq_one, ENNReal.ofReal_one, one_mul]
      _ = ∑ k, ∫⁻ w in (B.chart j).target, ENNReal.ofReal
          (hne.some.χ k ((B.chart j).symm w)) *
            (g ((B.chart j).symm w) * ‖locDens B (fun _ => Ψ) j w‖ₑ) :=
          lintegral_finsetSum' _ hmeas
      _ ≤ _ := Finset.sum_le_sum fun k _ => move_le B Ψ hΨ _ k j (fun y hy =>
          image_eq_zero_of_notMem_tsupport (fun h => hy (hne.some.tsupport_subset k h))) g
  calc chartSumInt B Ψ U g ≤ ∑ _j : Fin B.n, ∑ k, ∫⁻ z in (B.chart k).target,
        ENNReal.ofReal (hne.some.χ k ((B.chart k).symm z)) *
          (g ((B.chart k).symm z) * ‖locDens B (fun _ => Ψ) k z‖ₑ) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory.ChartSumBound
