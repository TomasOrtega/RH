import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

open MeasureTheory Metric Set Filter Topology Real

namespace ReciprocityTheory.AnForm.A.PshMean

noncomputable section

variable {D : ℕ}

/- English proof (translation)
Set `f : ℂ →ₗ[ℝ] ℂ` to `Algebra.lmul ℝ ℂ c`. Establish `hf : (fun ζ : ℂ => c * ζ) = ⇑f` using `rfl`. Establish `hdet : LinearMap.det f = 1`. Establish `: LinearMap.det f = Algebra.norm ℝ c` using `(Algebra.norm_apply ℝ c).symm`. Rewrite using `[this, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hc]`.

Evaluate the numerical expressions. Use `⟨(continuous_const.mul continuous_id).measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]`. Simplify using the standard rewrite rules.
-/
lemma mul_mp (c : ℂ) (hc : ‖c‖ = 1) : MeasurePreserving (fun ζ : ℂ => c * ζ) volume volume := by
  let f : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ c
  have hf : (fun ζ : ℂ => c * ζ) = ⇑f := rfl
  have hdet : LinearMap.det f = 1 := by
    have : LinearMap.det f = Algebra.norm ℝ c := (Algebra.norm_apply ℝ c).symm
    rw [this, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hc]
    norm_num
  refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

/- English proof (translation)
The claim follows from `measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => mul_mp c hc)`.
-/
lemma smul_mp (c : ℂ) (hc : ‖c‖ = 1) :
    MeasurePreserving (fun v : Fin D → ℂ => c • v) volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => mul_mp c hc)

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `x ⟨hx, hxU⟩`. Establish `h` using `hφ x hxU y hx`. Rewrite `h` using `[nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)]`. Use `filter_upwards [h, hU.mem_nhds hxU] with x' h1 h2`.

Conclude with `⟨h1, h2⟩`.
-/
lemma isOpen_inter_preimage {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) (y : ℝ) : IsOpen (φ ⁻¹' Iio y ∩ U) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hx, hxU⟩
  have h := hφ x hxU y hx
  rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h
  filter_upwards [h, hU.mem_nhds hxU] with x' h1 h2
  exact ⟨h1, h2⟩

/- English proof (translation)
Use `measurable_of_Iio fun y => ?_` and prove the remaining obligations. Rewrite using `[Set.indicator_preimage]`. Conclude with `(isOpen_inter_preimage hU hφ y).measurableSet.union ((measurable_zero measurableSet_Iio).diff hU.measurableSet)`.
-/
lemma measurable_piecewise {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) : Measurable (U.indicator φ) := by
  refine measurable_of_Iio fun y => ?_
  rw [Set.indicator_preimage]
  exact (isOpen_inter_preimage hU hφ y).measurableSet.union
    ((measurable_zero measurableSet_Iio).diff hU.measurableSet)

/- English proof (translation)
Introduce `D U φ z t hU hφ ht hK`. Use `set K := closedBall z t with hKdef`. Establish `hKc : IsCompact K` using `isCompact_closedBall z t`. Establish `hKm : MeasurableSet K` using `measurableSet_closedBall`. Establish `hzK : z ∈ K` using `mem_closedBall_self ht.le`.

Take `⟨x0, -, hx0⟩` from `(hφ.1.mono hK).exists_isMaxOn ⟨z, hzK⟩ hKc`. Use `set M := φ x0 with hMdef`. Establish `hM : ∀ x ∈ K, φ x ≤ M` using `fun x hx => hx0 hx`. Use `set φU := U.indicator φ with hφUdef`. Establish `hφUm : Measurable φU` using `measurable_piecewise hU hφ.1`.

Establish `hφU : ∀ x ∈ K, φU x = φ x` using `fun x hx => Set.indicator_of_mem (hK hx) φ`. Use `set Φ : (Fin D → ℂ) → ENNReal := fun x => ENNReal.ofReal (M - φU x) with hΦdef`. Establish `hΦm : Measurable Φ` using `ENNReal.measurable_ofReal.comp (measurable_const.sub hφUm)`. Use `set k : (Fin D → ℂ) → ENNReal := fun v => K.indicator Φ (z + v) with hkdef`. Establish `hkm : Measurable k` using `(hΦm.indicator hKm).comp (measurable_const_add z)`.

Establish `hk : ∫⁻ v, k v = ∫⁻ x in K, Φ x`. Rewrite using `[lintegral_add_left_eq_self (fun x => K.indicator Φ x) z, lintegral_indicator hKm]`. Establish `memK : ∀ (c : ℂ) (v : Fin D → ℂ), ‖c‖ = 1 → (z + c • v ∈ K ↔ z + v ∈ K)`. Introduce `c v hc`. Simplify using `[K, mem_closedBall, dist_eq_norm, norm_smul, hc]`.

Establish `hrot : ∀ θ : ℝ, ∫⁻ v, k (circleMap 0 1 θ • v) = ∫⁻ v, k v` using `fun θ => (smul_mp _ (by simp)).lintegral_comp hkm`. Establish `hθ : ∀ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) ≤ K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) (z + v)`. Introduce `v`. Distinguish the cases in `hv : z + v ∈ K`. Rewrite using `[Set.indicator_of_mem hv]`.

Establish `hvt : ‖v‖ ≤ t` using `by simpa [K, mem_closedBall, dist_eq_norm] using hv`. Establish `hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • v ∈ U`. Introduce `ζ hζ`. Apply `hK` to reduce the goal to its premises. Simplify using `only [K, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]`.

Use polynomial arithmetic with `[norm_nonneg ζ, norm_nonneg v]`. Take `⟨hci, hsub⟩` from `hφ.2 z v hdisc`. Establish `hmemθ : ∀ θ : ℝ, z + circleMap 0 1 θ • v ∈ K` using `fun θ => (memK _ v (by simp)).2 hv`. Establish `hkθ : ∀ θ : ℝ, k (circleMap 0 1 θ • v) = ENNReal.ofReal (M - φ (z + circleMap 0 1 θ • v))`. Introduce `θ`.

Simplify using `only [k, Φ]`. Rewrite using `[Set.indicator_of_mem (hmemθ θ), hφU _ (hmemθ θ)]`. Establish `hci' : IntegrableOn (fun θ : ℝ => φ (z + circleMap 0 1 θ • v)) (Ioc 0 (2 * π))` using `hci.1`. Establish `hconst : IntegrableOn (fun _ : ℝ => M) (Ioc 0 (2 * π))` using `continuous_const.integrableOn_Ioc`. Establish `hint : IntegrableOn (fun θ : ℝ => M - φ (z + circleMap 0 1 θ • v)) (Ioc 0 (2 * π))` using `hconst.sub hci'`.

Rewrite using `[lintegral_congr (fun θ => hkθ θ), ← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioc fun θ _ => sub_nonneg.2 (hM _ (hmemθ θ)))]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[integral_sub hconst hci', setIntegral_const]`. Rewrite `hsub` using `[Real.circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul]`. Establish `hvol : volume.real (Ioc (0:ℝ) (2 * π)) = 2 * π`.

Simplify using `[Real.volume_real_Ioc, two_pi_pos.le]`. Rewrite using `[hvol, smul_eq_mul]`. Establish `h2 : 0 < 2 * π` using `two_pi_pos`. Establish `h3` using `(le_inv_mul_iff₀ h2).1 hsub`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[Set.indicator_of_notMem hv]`. Establish `h0 : ∀ θ : ℝ, k (circleMap 0 1 θ • v) = 0` using `fun θ => Set.indicator_of_notMem (fun h => hv ((memK _ v (by simp)).1 h)) _`. Simplify using `[h0]`. Establish `hswap : ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ v, k (circleMap 0 1 θ • v) = ∫⁻ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v)` using `lintegral_lintegral_swap ((hkm.comp (by fun_prop : Continuous fun p : ℝ × (Fin D → ℂ) => circleMap 0 1 p.1 • p.2).measurable).aemeasurable)`. Establish `hmain : ENNReal.ofReal (2 * π) * ∫⁻ v, k v ≤ ENNReal.ofReal (2 * π * (M - φ z)) * volume K`.

Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[hrot]`. Rewrite using `[lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_comm]`. Use `_ = ∫⁻ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) := hswap`. Use `_ ≤ ∫⁻ v, K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) (z + v) := lintegral_mono hθ`.

Use `_ = ENNReal.ofReal (2 * π * (M - φ z)) * volume K := by`. Rewrite using `[lintegral_add_left_eq_self (fun x => K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) x) z, lintegral_indicator_const hKm]`. Establish `hbound : ∫⁻ x in K, Φ x ≤ ENNReal.ofReal (M - φ z) * volume K`. Rewrite using `[← hk]`. Rewrite `hmain` using `[ENNReal.ofReal_mul two_pi_pos.le, mul_assoc]`.

Rewrite `hmain` using `[mul_comm (ENNReal.ofReal (2 * π)), mul_comm (ENNReal.ofReal (2 * π))]`. Conclude with `(ENNReal.mul_le_mul_iff_left (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top).1 hmain`. Establish `hKfin : volume K < ⊤` using `measure_closedBall_lt_top`. Establish `hKpos : 0 < volume K` using `measure_closedBall_pos volume z ht`. Establish `hconstK : IntegrableOn (fun _ : Fin D → ℂ => M) K` using `continuous_const.continuousOn.integrableOn_compact hKc`.

Establish `hψint : IntegrableOn (fun x => M - φU x) K`. Use `⟨(measurable_const.sub hφUm).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[HasFiniteIntegral]`. Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_congr_fun hKm (fun x hx => ?_)` and prove the remaining obligations.

Rewrite using `[Real.enorm_of_nonneg (sub_nonneg.2 ((hφU x hx).symm ▸ hM x hx))]`. Use `_ ≤ _ := hbound`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin`. Establish `hφint : IntegrableOn φ K`. Use `(hconstK.sub hψint).congr_fun (fun x hx => ?_) hKm` and prove the remaining obligations.

Simplify using `[hφU x hx]`. Use `⟨hφint, ?_⟩` and prove the remaining obligations. Establish `hreal : ∫ x in K, (M - φU x) ≤ (M - φ z) * volume.real K`. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hKm (fun x hx => sub_nonneg.2 ((hφU x hx).symm ▸ hM x hx))) hψint.aestronglyMeasurable]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 (hM z hzK))]`. Both sides reduce to the same expression. Establish `hsplit : ∫ x in K, (M - φU x) = M * volume.real K - ∫ x in K, φ x`. Rewrite using `[integral_sub hconstK (hφint.congr_fun (fun x hx => (hφU x hx).symm) hKm), setIntegral_const, smul_eq_mul, mul_comm]`. Use `congr 1`.

Conclude with `setIntegral_congr_fun hKm (fun x hx => hφU x hx)`. Establish `hKr : 0 < volume.real K` using `ENNReal.toReal_pos hKpos.ne' hKfin.ne`. Rewrite using `[setAverage_eq, smul_eq_mul, le_inv_mul_iff₀ hKr]`. Use polynomial arithmetic with `[hreal, hsplit]`.
-/
theorem subMeanValuePolydisc_holds : SubMeanPolydiscStatement := by
  intro D U φ z t hU hφ ht hK
  set K := closedBall z t with hKdef
  have hKc : IsCompact K := isCompact_closedBall z t
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hzK : z ∈ K := mem_closedBall_self ht.le
  obtain ⟨x0, -, hx0⟩ := (hφ.1.mono hK).exists_isMaxOn ⟨z, hzK⟩ hKc
  set M := φ x0 with hMdef
  have hM : ∀ x ∈ K, φ x ≤ M := fun x hx => hx0 hx
  set φU := U.indicator φ with hφUdef
  have hφUm : Measurable φU := measurable_piecewise hU hφ.1
  have hφU : ∀ x ∈ K, φU x = φ x := fun x hx => Set.indicator_of_mem (hK hx) φ
  set Φ : (Fin D → ℂ) → ENNReal := fun x => ENNReal.ofReal (M - φU x) with hΦdef
  have hΦm : Measurable Φ := ENNReal.measurable_ofReal.comp (measurable_const.sub hφUm)
  set k : (Fin D → ℂ) → ENNReal := fun v => K.indicator Φ (z + v) with hkdef
  have hkm : Measurable k := (hΦm.indicator hKm).comp (measurable_const_add z)
  have hk : ∫⁻ v, k v = ∫⁻ x in K, Φ x := by
    rw [lintegral_add_left_eq_self (fun x => K.indicator Φ x) z, lintegral_indicator hKm]
  have memK : ∀ (c : ℂ) (v : Fin D → ℂ), ‖c‖ = 1 → (z + c • v ∈ K ↔ z + v ∈ K) := by
    intro c v hc
    simp [K, mem_closedBall, dist_eq_norm, norm_smul, hc]
  have hrot : ∀ θ : ℝ, ∫⁻ v, k (circleMap 0 1 θ • v) = ∫⁻ v, k v := fun θ =>
    (smul_mp _ (by simp)).lintegral_comp hkm
  have hθ : ∀ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) ≤
      K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) (z + v) := by
    intro v
    by_cases hv : z + v ∈ K
    · rw [Set.indicator_of_mem hv]
      have hvt : ‖v‖ ≤ t := by simpa [K, mem_closedBall, dist_eq_norm] using hv
      have hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • v ∈ U := by
        intro ζ hζ
        apply hK
        simp only [K, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
        nlinarith [norm_nonneg ζ, norm_nonneg v]
      obtain ⟨hci, hsub⟩ := hφ.2 z v hdisc
      have hmemθ : ∀ θ : ℝ, z + circleMap 0 1 θ • v ∈ K := fun θ => (memK _ v (by simp)).2 hv
      have hkθ : ∀ θ : ℝ, k (circleMap 0 1 θ • v) =
          ENNReal.ofReal (M - φ (z + circleMap 0 1 θ • v)) := by
        intro θ
        simp only [k, Φ]
        rw [Set.indicator_of_mem (hmemθ θ), hφU _ (hmemθ θ)]
      have hci' : IntegrableOn (fun θ : ℝ => φ (z + circleMap 0 1 θ • v)) (Ioc 0 (2 * π)) :=
        hci.1
      have hconst : IntegrableOn (fun _ : ℝ => M) (Ioc 0 (2 * π)) :=
        continuous_const.integrableOn_Ioc
      have hint : IntegrableOn (fun θ : ℝ => M - φ (z + circleMap 0 1 θ • v)) (Ioc 0 (2 * π)) :=
        hconst.sub hci'
      rw [lintegral_congr (fun θ => hkθ θ), ← ofReal_integral_eq_lintegral_ofReal hint
        (ae_restrict_of_forall_mem measurableSet_Ioc fun θ _ => sub_nonneg.2 (hM _ (hmemθ θ)))]
      apply ENNReal.ofReal_le_ofReal
      rw [integral_sub hconst hci', setIntegral_const]
      rw [Real.circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul] at hsub
      have hvol : volume.real (Ioc (0:ℝ) (2 * π)) = 2 * π := by
        simp [Real.volume_real_Ioc, two_pi_pos.le]
      rw [hvol, smul_eq_mul]
      have h2 : 0 < 2 * π := two_pi_pos
      have h3 := (le_inv_mul_iff₀ h2).1 hsub
      nlinarith
    · rw [Set.indicator_of_notMem hv]
      have h0 : ∀ θ : ℝ, k (circleMap 0 1 θ • v) = 0 := fun θ =>
        Set.indicator_of_notMem (fun h => hv ((memK _ v (by simp)).1 h)) _
      simp [h0]
  have hswap : ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ v, k (circleMap 0 1 θ • v) =
      ∫⁻ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) :=
    lintegral_lintegral_swap ((hkm.comp (by fun_prop :
      Continuous fun p : ℝ × (Fin D → ℂ) => circleMap 0 1 p.1 • p.2).measurable).aemeasurable)
  have hmain : ENNReal.ofReal (2 * π) * ∫⁻ v, k v ≤
      ENNReal.ofReal (2 * π * (M - φ z)) * volume K := by
    calc ENNReal.ofReal (2 * π) * ∫⁻ v, k v
        = ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ v, k (circleMap 0 1 θ • v) := by
          simp_rw [hrot]
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_comm]
      _ = ∫⁻ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) := hswap
      _ ≤ ∫⁻ v, K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) (z + v) :=
          lintegral_mono hθ
      _ = ENNReal.ofReal (2 * π * (M - φ z)) * volume K := by
          rw [lintegral_add_left_eq_self
            (fun x => K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) x) z,
            lintegral_indicator_const hKm]
  have hbound : ∫⁻ x in K, Φ x ≤ ENNReal.ofReal (M - φ z) * volume K := by
    rw [← hk]
    rw [ENNReal.ofReal_mul two_pi_pos.le, mul_assoc] at hmain
    rw [mul_comm (ENNReal.ofReal (2 * π)), mul_comm (ENNReal.ofReal (2 * π))] at hmain
    exact (ENNReal.mul_le_mul_iff_left (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top).1 hmain
  have hKfin : volume K < ⊤ := measure_closedBall_lt_top
  have hKpos : 0 < volume K := measure_closedBall_pos volume z ht
  have hconstK : IntegrableOn (fun _ : Fin D → ℂ => M) K := continuous_const.continuousOn.integrableOn_compact hKc
  have hψint : IntegrableOn (fun x => M - φU x) K := by
    refine ⟨(measurable_const.sub hφUm).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ x in K, ‖M - φU x‖ₑ = ∫⁻ x in K, Φ x := by
          refine setLIntegral_congr_fun hKm (fun x hx => ?_)
          rw [Real.enorm_of_nonneg (sub_nonneg.2 ((hφU x hx).symm ▸ hM x hx))]
      _ ≤ _ := hbound
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin
  have hφint : IntegrableOn φ K := by
    refine (hconstK.sub hψint).congr_fun (fun x hx => ?_) hKm
    simp [hφU x hx]
  refine ⟨hφint, ?_⟩
  have hreal : ∫ x in K, (M - φU x) ≤ (M - φ z) * volume.real K := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hKm
      (fun x hx => sub_nonneg.2 ((hφU x hx).symm ▸ hM x hx))) hψint.aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal (M - φ z) * volume K).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin).ne hbound
      _ = _ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 (hM z hzK))]
          rfl
  have hsplit : ∫ x in K, (M - φU x) = M * volume.real K - ∫ x in K, φ x := by
    rw [integral_sub hconstK (hφint.congr_fun (fun x hx => (hφU x hx).symm) hKm),
      setIntegral_const, smul_eq_mul, mul_comm]
    congr 1
    exact setIntegral_congr_fun hKm (fun x hx => hφU x hx)
  have hKr : 0 < volume.real K := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  rw [setAverage_eq, smul_eq_mul, le_inv_mul_iff₀ hKr]
  nlinarith [hreal, hsplit]

/- English proof (translation)
Introduce `D U φ hU hφ x hx`. Take `⟨r, hr, hrU⟩` from `Metric.isOpen_iff.1 hU x hx`. Use `⟨closedBall x (r / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), (subMeanValuePolydisc_holds D U φ x (r / 2) hU hφ (half_pos hr) ((closedBall_subset_ball (by linarith)).trans hrU)).1⟩` and prove the remaining obligations.
-/
theorem plurisubharmonicLocallyIntegrable_holds : IsPsh_locallyIntegrableStatement := by
  intro D U φ hU hφ x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨closedBall x (r / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)),
    (subMeanValuePolydisc_holds D U φ x (r / 2) hU hφ (half_pos hr)
      ((closedBall_subset_ball (by linarith)).trans hrU)).1⟩

end

end ReciprocityTheory.AnForm.A.PshMean

open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff

namespace ReciprocityTheory.AnForm.A.PshMol

noncomputable section

def b0 : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def g0 (D : ℕ) (w : Fin D → ℂ) : ℝ := b0 (∑ i, ‖w i‖ ^ 2)

/- English proof (translation)
The claim follows from `b0.contDiff.comp (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))`.
-/
lemma radialBump_contDiff (D : ℕ) : ContDiff ℝ ∞ (g0 D) :=
  b0.contDiff.comp (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))

/- English proof (translation)
The claim follows from `b0.nonneg`.
-/
lemma radialBump_nonneg (D : ℕ) (w : Fin D → ℂ) : 0 ≤ g0 D w := b0.nonneg

/- English proof (translation)
Introduce `w hw`. Establish `h : (∑ i, ‖w i‖ ^ 2) ∈ ball (0:ℝ) (1 / 4)`. Use `b0.support_eq ▸ (show (∑ i, ‖w i‖ ^ 2) ∈ Function.support b0 from hw)` as an intermediate fact. Simplify `this` using `[b0]`. Rewrite `h` using `[mem_ball, dist_zero_right, Real.norm_eq_abs]`.

Rewrite using `[mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]`. Introduce `i`. Establish `h1 : ‖w i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2` using `Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)`. Establish `h2` using `le_abs_self (∑ j, ‖w j‖ ^ 2)`. Use polynomial arithmetic with `[norm_nonneg (w i)]`.
-/
lemma radialBump_support (D : ℕ) : Function.support (g0 D) ⊆ ball 0 1 := by
  intro w hw
  have h : (∑ i, ‖w i‖ ^ 2) ∈ ball (0:ℝ) (1 / 4) := by
    have := b0.support_eq ▸ (show (∑ i, ‖w i‖ ^ 2) ∈ Function.support b0 from hw)
    simpa [b0] using this
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at h
  rw [mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖w i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 := le_abs_self (∑ j, ‖w j‖ ^ 2)
  nlinarith [norm_nonneg (w i)]

/- English proof (translation)
Simplify using `[g0, norm_mul, hc]`.
-/
lemma radialBump_smul (D : ℕ) (c : ℂ) (w : Fin D → ℂ) (hc : ‖c‖ = 1) : g0 D (c • w) = g0 D w := by
  simp [g0, norm_mul, hc]

/- English proof (translation)
The claim follows from `HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) 1) fun w hw => by by_contra h exact hw (ball_subset_closedBall (radialBump_support D h))`.
-/
lemma radialBump_hasCompactSupport (D : ℕ) : HasCompactSupport (g0 D) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) 1) fun w hw => by
    by_contra h
    exact hw (ball_subset_closedBall (radialBump_support D h))

/- English proof (translation)
The claim follows from `(radialBump_contDiff D).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (radialBump_hasCompactSupport D) (radialBump_nonneg D) (by rw [g0, b0.one_of_mem_closedBall] · norm_num · simp [b0])`.
-/
lemma integral_radialBump_pos (D : ℕ) : 0 < ∫ w, g0 D w :=
  (radialBump_contDiff D).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (radialBump_hasCompactSupport D)
    (radialBump_nonneg D) (by
      rw [g0, b0.one_of_mem_closedBall]
      · norm_num
      · simp [b0])

/- English proof (translation)
Introduce `D` and use `⟨{ toFun := fun w => (∫ v, g0 D v)⁻¹ * g0 D w contDiff := contDiff_const.mul (radialBump_contDiff D) nonneg := fun w => mul_nonneg (inv_nonneg.2 (integral_radialBump_pos D).le) (radialBump_nonneg D w) support_subset := fun w hw => radialBump_support D (fun h => hw (by simp [h])) …`.
-/
theorem circleInvariantMollifierExists_holds : MollifierInhabitStatement := fun D =>
  ⟨{ toFun := fun w => (∫ v, g0 D v)⁻¹ * g0 D w
     contDiff := contDiff_const.mul (radialBump_contDiff D)
     nonneg := fun w => mul_nonneg (inv_nonneg.2 (integral_radialBump_pos D).le) (radialBump_nonneg D w)
     support_subset := fun w hw => radialBump_support D (fun h => hw (by simp [h]))
     integral_eq_one := by
       rw [integral_const_mul, inv_mul_cancel₀ (integral_radialBump_pos D).ne']
     circle_inv := fun c w hc => by simp only [radialBump_smul D c w hc] }⟩

end

end ReciprocityTheory.AnForm.A.PshMol
