import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUDensity
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KDensB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KDensC

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
The claim follows from `Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity`.
-/
lemma kd_volU_pos (M : ℕ) : 0 < volU M :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

def kdTM {N : ℕ} (u : UNgrp N) : Fin N → Fin N → ℂ := Matrix.of.symm (toM u)

/- English proof (translation)
The claim follows from `continuous_toM _`.
-/
lemma continuous_kdTM {N : ℕ} : Continuous (kdTM (N := N)) := continuous_toM _

/- English proof (translation)
Take `⟨δ, hδ, hd⟩` from `volU_density μ η hη`. Take `⟨r, hr, hinj⟩` from `kdF_injOn (N := N)`. Use `⟨min δ r, lt_min hδ hr, hinj.mono (Metric.ball_subset_ball (min_le_right _ _)), ?_⟩` and prove the remaining obligations. Introduce `A hA hAm`. Establish `hAr : A ⊆ Metric.ball 0 r` using `hA.trans (Metric.ball_subset_ball (min_le_right _ _))`.

Establish `hmeas : MeasurableSet (kdF N '' A)` using `hAm.image_of_continuousOn_injOn continuous_kdF.continuousOn (hinj.mono hAr)`. Establish `e : kdTM ⁻¹' (kdF N '' A) = {k : UNgrp N | ∃ x ∈ A, toM k = NormedSpace.exp (skMat x)}`. Use extensionality with `k`. Simplify using `only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, h⟩`. Conclude with `⟨x, hx, (Matrix.of.symm.injective h).symm⟩`. Introduce and unpack `⟨x, hx, h⟩; exact ⟨x, hx, by rw [kdF, kdTM, h]⟩`. Rewrite using `[Measure.map_apply continuous_kdTM.measurable hmeas, e]`. Use `hd A hAm fun x hx => ?_` and prove the remaining obligations.

Use `hA hx` as an intermediate fact. Rewrite `this` using `[Metric.mem_ball, dist_zero_right]`. Conclude with `this.trans_le (min_le_left _ _)`.
-/
lemma kd_factor {N : ℕ} (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (η : ℝ)
    (hη : 0 < η) : ∃ r > 0, Set.InjOn (kdF N) (Metric.ball 0 r) ∧
      ∀ A ⊆ Metric.ball (0 : UCo N) r, MeasurableSet A →
        (μ.map kdTM) (kdF N '' A) ≤ ENNReal.ofReal ((1 + η) / volU N) * volume A ∧
          ENNReal.ofReal ((1 - η) / volU N) * volume A ≤ (μ.map kdTM) (kdF N '' A) := by
  obtain ⟨δ, hδ, hd⟩ := volU_density μ η hη
  obtain ⟨r, hr, hinj⟩ := kdF_injOn (N := N)
  refine ⟨min δ r, lt_min hδ hr, hinj.mono (Metric.ball_subset_ball (min_le_right _ _)), ?_⟩
  intro A hA hAm
  have hAr : A ⊆ Metric.ball 0 r := hA.trans (Metric.ball_subset_ball (min_le_right _ _))
  have hmeas : MeasurableSet (kdF N '' A) :=
    hAm.image_of_continuousOn_injOn continuous_kdF.continuousOn (hinj.mono hAr)
  have e : kdTM ⁻¹' (kdF N '' A) = {k : UNgrp N | ∃ x ∈ A, toM k = NormedSpace.exp (skMat x)} := by
    ext k
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (Matrix.of.symm.injective h).symm⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, by rw [kdF, kdTM, h]⟩
  rw [Measure.map_apply continuous_kdTM.measurable hmeas, e]
  refine hd A hAm fun x hx => ?_
  have := hA hx
  rw [Metric.mem_ball, dist_zero_right] at this
  exact this.trans_le (min_le_left _ _)

/- English proof (translation)
The claim follows from `hB.image_of_continuousOn_injOn hf hi`.
-/
lemma kd_meas_image_prod {E₁ E₂ X : Type*} [TopologicalSpace E₁] [PolishSpace E₁] [MeasurableSpace E₁]
    [BorelSpace E₁] [TopologicalSpace E₂] [PolishSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] {f : E₁ × E₂ → X}
    {B : Set (E₁ × E₂)} (hB : MeasurableSet B) (hf : ContinuousOn f B) (hi : Set.InjOn f B) :
    MeasurableSet (f '' B) :=
  hB.image_of_continuousOn_injOn hf hi

/- English proof (translation)
Take `⟨μp, hHp, hPp⟩` from `unGrp_haarProb_exists (pOf ε)`. Take `⟨μq, hHq, hPq⟩` from `unGrp_haarProb_exists (qOf ε)`. Use `set η' : ℝ := min (η / 3) (1 / 2) with hη'def`. Establish `hη'0 : 0 < η'` using `lt_min (by linarith) (by norm_num)`. Establish `hη'1 : η' ≤ η / 3` using `min_le_left _ _`.

Establish `hη'2 : η' ≤ 1 / 2` using `min_le_right _ _`. Take `⟨rp, hrp, hip, hp⟩` from `kd_factor μp η' hη'0`. Take `⟨rq, hrq, hiq, hq⟩` from `kd_factor μq η' hη'0`. Use `⟨min rp rq, lt_min hrp hrq, fun B hB hBδ => ?_⟩` and prove the remaining obligations. Use `set S := {k : KG ε | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} with hS`.

Use `set B' : Set (UCo (pOf ε) × UCo (qOf ε)) := kdT ε '' B with hB'`. Establish `hB'm : MeasurableSet B'` using `(kdT ε).measurableSet_image.2 hB`. Establish `hvol : volume B' = volume B`. Rewrite using `[hB', MeasurableEquiv.image_eq_preimage_symm]`. Conclude with `(MeasurePreserving.symm _ (kdT_mp ε)).measure_preimage hB.nullMeasurableSet`.

Establish `hB'U : B' ⊆ Metric.ball 0 rp ×ˢ Metric.ball 0 rq`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `h1` using `hBδ w hw`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_zero_right, kdT_fst]`.

Conclude with `(norm_kdCoS_le w true).trans_lt (h1.trans_le (min_le_left _ _))`. Rewrite using `[Metric.mem_ball, dist_zero_right, kdT_snd]`. Conclude with `(norm_kdCoS_le w false).trans_lt (h1.trans_le (min_le_right _ _))`. Establish `hpre : (kdPsi ε) ⁻¹' S = Prod.map kdTM kdTM ⁻¹' (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B')`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, hS, Set.mem_ofPred_eq, Set.mem_image, hB']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, he⟩`. Rewrite `he` using `[toMK_kdPsi, kMat_eq_kdD, exp_kdD]`. Establish `he'` using `kdD_injective ε he`.

Use `⟨kdT ε w, ⟨w, hw, rfl⟩, Prod.ext ?_ ?_⟩` and prove the remaining obligations. Use `show Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).1)) = Matrix.of.symm (toM x.1)`. Rewrite using `[kdT_fst]`. Conclude with `congrArg _ (congrFun he' true).symm`. Use `show Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).2)) = Matrix.of.symm (toM x.2)`.

Rewrite using `[kdT_snd]`. Conclude with `congrArg _ (congrFun he' false).symm`. Introduce and unpack `⟨z, ⟨w, hw, rfl⟩, hz⟩`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Establish `h1 : Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).1)) = Matrix.of.symm (toM x.1)` using `congrArg Prod.fst hz`.

Establish `h2 : Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).2)) = Matrix.of.symm (toM x.2)` using `congrArg Prod.snd hz`. Rewrite `h1` using `[kdT_fst]`. Rewrite `h2` using `[kdT_snd]`. Rewrite using `[toMK_kdPsi, kMat_eq_kdD, exp_kdD]`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Consider the cases of `s`. Conclude with `(Matrix.of.symm.injective h2).symm`. Conclude with `(Matrix.of.symm.injective h1).symm`. Establish `hYm : MeasurableSet (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B')` using `kd_meas_image_prod hB'm (continuous_kdF.prodMap continuous_kdF).continuousOn ((hip.prodMap hiq).mono hB'U)`.

Establish `hdk : dk ε S = ((μp.map kdTM).prod (μq.map kdTM)) (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B')`. Rewrite using `[kd_dk_eq_map ε μp μq]`. Establish `hc : (⇑(kdPsi ε)) = ⇑(kdHomeo ε).toMeasurableEquiv` using `rfl`. Rewrite using `[hc, MeasurableEquiv.map_apply, ← hc, hpre, Measure.map_prod_map _ _ continuous_kdTM.measurable continuous_kdTM.measurable, Measure.map_apply (continuous_kdTM.measurable.prodMap continuous_kdTM.measurable) hYm]`. Take `⟨hup, hlo⟩` from `kd_prod_bounds (m₁ := μp.map kdTM) (m₂ := μq.map kdTM) volume volume Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet continuous_kdF.continuousOn continuous_kdF.continuousOn hip hiq _ _ _ _ hp hq hB'm hB'U`.

Establish `hvp` using `kd_volU_pos (pOf ε)`. Establish `hvq` using `kd_volU_pos (qOf ε)`. Establish `hpq : 0 < volU (pOf ε) * volU (qOf ε)` using `mul_pos hvp hvq`. Establish `hvol' : (volume.prod volume) B' = volume B` using `hvol`. Rewrite `hup`, `hlo` using `[hvol']`.

Rewrite using `[hdk]`. Establish `hcu : ENNReal.ofReal ((1 + η') / volU (pOf ε)) * ENNReal.ofReal ((1 + η') / volU (qOf ε)) ≤ ENNReal.ofReal ((1 + η) / (volU (pOf ε) * volU (qOf ε)))`. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[div_mul_div_comm]`.

Conclude with `div_le_div_of_nonneg_right (by nlinarith) hpq.le`. Establish `hcl : ENNReal.ofReal ((1 - η) / (volU (pOf ε) * volU (qOf ε))) ≤ ENNReal.ofReal ((1 - η') / volU (pOf ε)) * ENNReal.ofReal ((1 - η') / volU (qOf ε))`. Rewrite using `[← ENNReal.ofReal_mul (div_nonneg (by linarith) hvp.le)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[div_mul_div_comm]`.

Conclude with `div_le_div_of_nonneg_right (by nlinarith) hpq.le`. Conclude with `⟨hup.trans (by gcongr), le_trans (by gcongr) hlo⟩`.
-/
theorem dk_density (ε : Fin n → Bool) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ B : Set (KCo ε), MeasurableSet B → (∀ w ∈ B, ‖w‖ < δ) →
      dk ε {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} ≤
          ENNReal.ofReal ((1 + η) / (volU (pOf ε) * volU (qOf ε))) * volume B ∧
        ENNReal.ofReal ((1 - η) / (volU (pOf ε) * volU (qOf ε))) * volume B ≤
          dk ε {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} := by
  obtain ⟨μp, hHp, hPp⟩ := unGrp_haarProb_exists (pOf ε)
  obtain ⟨μq, hHq, hPq⟩ := unGrp_haarProb_exists (qOf ε)
  set η' : ℝ := min (η / 3) (1 / 2) with hη'def
  have hη'0 : 0 < η' := lt_min (by linarith) (by norm_num)
  have hη'1 : η' ≤ η / 3 := min_le_left _ _
  have hη'2 : η' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨rp, hrp, hip, hp⟩ := kd_factor μp η' hη'0
  obtain ⟨rq, hrq, hiq, hq⟩ := kd_factor μq η' hη'0
  refine ⟨min rp rq, lt_min hrp hrq, fun B hB hBδ => ?_⟩
  set S := {k : KG ε | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} with hS
  set B' : Set (UCo (pOf ε) × UCo (qOf ε)) := kdT ε '' B with hB'
  have hB'm : MeasurableSet B' := (kdT ε).measurableSet_image.2 hB
  have hvol : volume B' = volume B := by
    rw [hB', MeasurableEquiv.image_eq_preimage_symm]
    exact (MeasurePreserving.symm _ (kdT_mp ε)).measure_preimage hB.nullMeasurableSet
  have hB'U : B' ⊆ Metric.ball 0 rp ×ˢ Metric.ball 0 rq := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hBδ w hw
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, kdT_fst]
      exact (norm_kdCoS_le w true).trans_lt (h1.trans_le (min_le_left _ _))
    · rw [Metric.mem_ball, dist_zero_right, kdT_snd]
      exact (norm_kdCoS_le w false).trans_lt (h1.trans_le (min_le_right _ _))
  have hpre : (kdPsi ε) ⁻¹' S = Prod.map kdTM kdTM ⁻¹' (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B') := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq, Set.mem_image, hB']
    constructor
    · rintro ⟨w, hw, he⟩
      rw [toMK_kdPsi, kMat_eq_kdD, exp_kdD] at he
      have he' := kdD_injective ε he
      refine ⟨kdT ε w, ⟨w, hw, rfl⟩, Prod.ext ?_ ?_⟩
      · show Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).1)) = Matrix.of.symm (toM x.1)
        rw [kdT_fst]; exact congrArg _ (congrFun he' true).symm
      · show Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).2)) = Matrix.of.symm (toM x.2)
        rw [kdT_snd]; exact congrArg _ (congrFun he' false).symm
    · rintro ⟨z, ⟨w, hw, rfl⟩, hz⟩
      refine ⟨w, hw, ?_⟩
      have h1 : Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).1)) = Matrix.of.symm (toM x.1) :=
        congrArg Prod.fst hz
      have h2 : Matrix.of.symm (NormedSpace.exp (skMat (kdT ε w).2)) = Matrix.of.symm (toM x.2) :=
        congrArg Prod.snd hz
      rw [kdT_fst] at h1
      rw [kdT_snd] at h2
      rw [toMK_kdPsi, kMat_eq_kdD, exp_kdD]
      congr 1
      funext s
      cases s
      · exact (Matrix.of.symm.injective h2).symm
      · exact (Matrix.of.symm.injective h1).symm
  have hYm : MeasurableSet (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B') :=
    kd_meas_image_prod hB'm (continuous_kdF.prodMap continuous_kdF).continuousOn
      ((hip.prodMap hiq).mono hB'U)
  have hdk : dk ε S = ((μp.map kdTM).prod (μq.map kdTM)) (Prod.map (kdF (pOf ε)) (kdF (qOf ε)) '' B') := by
    rw [kd_dk_eq_map ε μp μq]
    have hc : (⇑(kdPsi ε)) = ⇑(kdHomeo ε).toMeasurableEquiv := rfl
    rw [hc, MeasurableEquiv.map_apply, ← hc, hpre,
      Measure.map_prod_map _ _ continuous_kdTM.measurable continuous_kdTM.measurable,
      Measure.map_apply (continuous_kdTM.measurable.prodMap continuous_kdTM.measurable) hYm]
  obtain ⟨hup, hlo⟩ := kd_prod_bounds (m₁ := μp.map kdTM) (m₂ := μq.map kdTM) volume volume
    Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet continuous_kdF.continuousOn
    continuous_kdF.continuousOn hip hiq _ _ _ _ hp hq hB'm hB'U
  have hvp := kd_volU_pos (pOf ε)
  have hvq := kd_volU_pos (qOf ε)
  have hpq : 0 < volU (pOf ε) * volU (qOf ε) := mul_pos hvp hvq
  have hvol' : (volume.prod volume) B' = volume B := hvol
  rw [hvol'] at hup hlo
  rw [hdk]
  have hcu : ENNReal.ofReal ((1 + η') / volU (pOf ε)) * ENNReal.ofReal ((1 + η') / volU (qOf ε)) ≤
      ENNReal.ofReal ((1 + η) / (volU (pOf ε) * volU (qOf ε))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_div_comm]
    exact div_le_div_of_nonneg_right (by nlinarith) hpq.le
  have hcl : ENNReal.ofReal ((1 - η) / (volU (pOf ε) * volU (qOf ε))) ≤
      ENNReal.ofReal ((1 - η') / volU (pOf ε)) * ENNReal.ofReal ((1 - η') / volU (qOf ε)) := by
    rw [← ENNReal.ofReal_mul (div_nonneg (by linarith) hvp.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_div_comm]
    exact div_le_div_of_nonneg_right (by nlinarith) hpq.le
  exact ⟨hup.trans (by gcongr), le_trans (by gcongr) hlo⟩

end ReciprocityTheory.ChartRestriction.DS
