import Mathlib
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hpos : ∀ s ∈ Set.uIcc (0 : ℝ) 1, 1 - s + t ≠ 0`. Introduce `s hs`. Rewrite `hs` using `[Set.uIcc_of_le zero_le_one]`. Use `hs.2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc : ContinuousOn (fun s : ℝ => t / (1 - s + t) ^ 2) (Set.uIcc (0 : ℝ) 1)` using `ContinuousOn.div continuousOn_const (by fun_prop) (fun s hs => pow_ne_zero 2 (hpos s hs))`. Establish `hint : ∫ s in (0 : ℝ)..1, t / (1 - s + t) ^ 2 = t / (1 - 1 + t) - t / (1 - 0 + t)`. Use `intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => t / (1 - s + t)) ?_ hc.intervalIntegrable` and prove the remaining obligations. Introduce `s hs`. Establish `h1 : HasDerivAt (fun s : ℝ => 1 - s + t) (-1) s`.

Simplify using `using ((hasDerivAt_id s).const_sub 1).add_const t`. Establish `h2` using `(hasDerivAt_const s t).fun_div h1 (hpos s hs)`. Establish `h3 : (0 * (1 - s + t) - t * -1) / (1 - s + t) ^ 2 = t / (1 - s + t) ^ 2` using `by ring`. Conclude with `h3 ▸ h2`. Rewrite `hc` using `[Set.uIcc_of_le zero_le_one]`.

Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_compact isCompact_Icc) (Filter.Eventually.of_forall fun s => by positivity), integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hint]`. Apply `ENNReal.ofReal_le_one.2` to reduce the goal to its premises. Establish `: 0 ≤ t / (1 - 0 + t)` using `by positivity`. Establish `h3 : t / (1 - 1 + t) = 1`. Rewrite using `[sub_self, zero_add, div_self ht.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lintegral_concKernel_le_one {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (t / (1 - s + t) ^ 2) ≤ 1 := by
  have hpos : ∀ s ∈ Set.uIcc (0 : ℝ) 1, 1 - s + t ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have := hs.2
    linarith
  have hc : ContinuousOn (fun s : ℝ => t / (1 - s + t) ^ 2) (Set.uIcc (0 : ℝ) 1) :=
    ContinuousOn.div continuousOn_const (by fun_prop) (fun s hs => pow_ne_zero 2 (hpos s hs))
  have hint : ∫ s in (0 : ℝ)..1, t / (1 - s + t) ^ 2 = t / (1 - 1 + t) - t / (1 - 0 + t) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => t / (1 - s + t)) ?_
      hc.intervalIntegrable
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => 1 - s + t) (-1) s := by
      simpa using ((hasDerivAt_id s).const_sub 1).add_const t
    have h2 := (hasDerivAt_const s t).fun_div h1 (hpos s hs)
    have h3 : (0 * (1 - s + t) - t * -1) / (1 - s + t) ^ 2 = t / (1 - s + t) ^ 2 := by ring
    exact h3 ▸ h2
  rw [Set.uIcc_of_le zero_le_one] at hc
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun s => by positivity), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, hint]
  apply ENNReal.ofReal_le_one.2
  have : 0 ≤ t / (1 - 0 + t) := by positivity
  have h3 : t / (1 - 1 + t) = 1 := by
    rw [sub_self, zero_add, div_self ht.ne']
  linarith

/- English proof (translation)
Introduce `M _ _ _ _ ν K v D C hK hv hD h0 hC hle`. Establish `hKm : MeasurableSet K` using `hK.isClosed.measurableSet`. Establish `hvm : AEMeasurable v (ν.restrict K)` using `hv.aemeasurable hKm`. Establish `hmap : ∀ f : ℝ → ENNReal, Measurable f → ∫⁻ z in K, f (v z) ∂ν ≤ C * ∫⁻ s in Set.Icc (0 : ℝ) 1, f s`. Introduce `f hf`.

Rewrite using `[← lintegral_map' hf.aemeasurable hvm]`. Use `(lintegral_mono' hle le_rfl).trans ?_` and prove the remaining obligations. Rewrite using `[lintegral_smul_measure, smul_eq_mul]`. Establish `hone : ∫⁻ _z in K, (1 : ENNReal) ∂ν ≤ C`. Use `hmap (fun _ => 1) measurable_const` as an intermediate fact.

Simplify using `using this`. Establish `hae : ∀ᵐ z ∂(ν.restrict K), v z ∈ Set.Icc (0 : ℝ) 1`. Apply `ae_of_ae_map hvm (p := fun s => s ∈ Set.Icc (0 : ℝ) 1)` to reduce the goal to its premises. Apply `Measure.AbsolutelyContinuous.ae_le (Measure.absolutelyContinuous_of_le_smul hle)` to reduce the goal to its premises. Conclude with `ae_restrict_mem measurableSet_Icc`.

Take `⟨Mx, hMx⟩` from `hK.exists_bound_of_continuousOn hD`. Establish `key : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ t : ℝ, 0 < t → ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν ≤ ENNReal.ofReal (δ + B * t) * C`. Introduce `δ hδ`. Establish `hS : IsCompact (K ∩ D ⁻¹' Set.Ici δ)` using `hK.of_isClosed_subset (hD.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici) Set.inter_subset_left`. Choose the witnesses or unpack the hypotheses as in `⟨η, hη, hηS⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K ∩ D ⁻¹' Set.Ici δ, η ≤ |1 - v z| := by`.

Apply `hS.exists_forall_le' (f := fun z => |1 - v z|)` to reduce the goal to its premises. Conclude with `(continuousOn_const.sub (hv.mono Set.inter_subset_left)).abs`. Introduce and unpack `z ⟨hz, hz'⟩`. Use `abs_pos.2 fun h => ?_` and prove the remaining obligations. Use `h0 z hz (by linarith)` as an intermediate fact.

Simplify using `only [Set.mem_preimage, Set.mem_Ici] at hz'`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨|Mx| / η ^ 2, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hB : 0 ≤ |Mx| / η ^ 2 * t` using `by positivity`. Establish `hf : Measurable fun s : ℝ => ENNReal.ofReal (t / (1 - s + t) ^ 2)` using `by fun_prop`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae, ae_restrict_mem hKm] with z hz hzK`. Establish `hk : 0 ≤ t / (1 - v z + t) ^ 2` using `by positivity`. Rewrite using `[mul_one, ← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_add hB (by positivity)]`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Distinguish the cases in `hd : δ ≤ D z`. Establish `h1` using `hηS z ⟨hzK, hd⟩`. Rewrite `h1` using `[abs_of_nonneg (by linarith [hz.2])]`. Establish `h2 : t / (1 - v z + t) ^ 2 ≤ t / η ^ 2` using `by gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : D z ≤ |Mx|` using `(le_abs_self _).trans ((hMx z hzK).trans (le_abs_self _))`. Establish `h4 : t / (1 - v z + t) ^ 2 * D z ≤ t / η ^ 2 * |Mx|` using `mul_le_mul h2 h3 (by linarith) (by positivity)`. Establish `h5 : t / η ^ 2 * |Mx| = |Mx| / η ^ 2 * t` using `by ring`. Establish `h6 : 0 ≤ δ * (t / (1 - v z + t) ^ 2)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hd`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = ENNReal.ofReal (|Mx| / η ^ 2 * t) * ∫⁻ _z in K, (1 : ENNReal) ∂ν + ENNReal.ofReal δ * ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2) ∂ν := by`. Rewrite using `[lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`.

Use `_ ≤ ENNReal.ofReal (|Mx| / η ^ 2 * t) * C + ENNReal.ofReal δ * C := by gcongr`. Use `(hmap _ hf).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by`. Rewrite using `[ENNReal.ofReal_add hδ.le hB]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ENNReal.tendsto_nhds_zero]`. Introduce `ε hε`. Establish `hT : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x * C) (nhds 0) (nhds 0)`. Establish `h1 : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x) (nhds 0) (nhds 0)`.

Simplify using `using ENNReal.continuous_ofReal.tendsto 0`. Simplify using `using ENNReal.Tendsto.mul_const h1 (Or.inr hC)`. Establish `hev` using `hT.eventually (gt_mem_nhds hε)`. Take `⟨r, hr, hrb⟩` from `Metric.eventually_nhds_iff.1 hev`. Take `⟨B, hB⟩` from `key (r / 2) (by positivity)`.

Establish `hT2 : Filter.Tendsto (fun t : ℝ => r / 2 + B * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (r / 2))`. Apply `Filter.Tendsto.mono_left _ nhdsWithin_le_nhds` to reduce the goal to its premises. Establish `: Continuous (fun t : ℝ => r / 2 + B * t)` using `by fun_prop`. Simplify using `using this.tendsto 0`. Establish `hmem : Metric.ball (0 : ℝ) r ∈ nhds (r / 2)`.

Apply `Metric.isOpen_ball.mem_nhds` to reduce the goal to its premises. Rewrite using `[Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `filter_upwards [hT2.eventually hmem, self_mem_nhdsWithin] with t h1 h2`. Conclude with `(hB t h2).trans (hrb h1).le`.
-/
theorem tendsto_lintegral_concKernel_mul_zero :
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) (K : Set M) (v D : M → ℝ) (C : ENNReal),
    IsCompact K → ContinuousOn v K → ContinuousOn D K → (∀ z ∈ K, v z = 1 → D z = 0) → C ≠ ⊤ →
    Measure.map v (ν.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun t : ℝ => ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro M _ _ _ _ ν K v D C hK hv hD h0 hC hle
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hvm : AEMeasurable v (ν.restrict K) := hv.aemeasurable hKm
  have hmap : ∀ f : ℝ → ENNReal, Measurable f →
      ∫⁻ z in K, f (v z) ∂ν ≤ C * ∫⁻ s in Set.Icc (0 : ℝ) 1, f s := by
    intro f hf
    rw [← lintegral_map' hf.aemeasurable hvm]
    refine (lintegral_mono' hle le_rfl).trans ?_
    rw [lintegral_smul_measure, smul_eq_mul]
  have hone : ∫⁻ _z in K, (1 : ENNReal) ∂ν ≤ C := by
    have := hmap (fun _ => 1) measurable_const
    simpa using this
  have hae : ∀ᵐ z ∂(ν.restrict K), v z ∈ Set.Icc (0 : ℝ) 1 := by
    apply ae_of_ae_map hvm (p := fun s => s ∈ Set.Icc (0 : ℝ) 1)
    apply Measure.AbsolutelyContinuous.ae_le (Measure.absolutelyContinuous_of_le_smul hle)
    exact ae_restrict_mem measurableSet_Icc
  obtain ⟨Mx, hMx⟩ := hK.exists_bound_of_continuousOn hD
  have key : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ t : ℝ, 0 < t →
      ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν ≤
        ENNReal.ofReal (δ + B * t) * C := by
    intro δ hδ
    have hS : IsCompact (K ∩ D ⁻¹' Set.Ici δ) :=
      hK.of_isClosed_subset (hD.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
        Set.inter_subset_left
    obtain ⟨η, hη, hηS⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K ∩ D ⁻¹' Set.Ici δ, η ≤ |1 - v z| := by
      apply hS.exists_forall_le' (f := fun z => |1 - v z|)
      · exact (continuousOn_const.sub (hv.mono Set.inter_subset_left)).abs
      · rintro z ⟨hz, hz'⟩
        refine abs_pos.2 fun h => ?_
        have := h0 z hz (by linarith)
        simp only [Set.mem_preimage, Set.mem_Ici] at hz'
        linarith
    refine ⟨|Mx| / η ^ 2, fun t ht => ?_⟩
    have hB : 0 ≤ |Mx| / η ^ 2 * t := by positivity
    have hf : Measurable fun s : ℝ => ENNReal.ofReal (t / (1 - s + t) ^ 2) := by fun_prop
    calc ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν
        ≤ ∫⁻ z in K, (ENNReal.ofReal (|Mx| / η ^ 2 * t) * 1 +
            ENNReal.ofReal δ * ENNReal.ofReal (t / (1 - v z + t) ^ 2)) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae, ae_restrict_mem hKm] with z hz hzK
          have hk : 0 ≤ t / (1 - v z + t) ^ 2 := by positivity
          rw [mul_one, ← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_add hB (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          by_cases hd : δ ≤ D z
          · have h1 := hηS z ⟨hzK, hd⟩
            rw [abs_of_nonneg (by linarith [hz.2])] at h1
            have h2 : t / (1 - v z + t) ^ 2 ≤ t / η ^ 2 := by
              gcongr
              linarith
            have h3 : D z ≤ |Mx| := (le_abs_self _).trans ((hMx z hzK).trans (le_abs_self _))
            have h4 : t / (1 - v z + t) ^ 2 * D z ≤ t / η ^ 2 * |Mx| :=
              mul_le_mul h2 h3 (by linarith) (by positivity)
            have h5 : t / η ^ 2 * |Mx| = |Mx| / η ^ 2 * t := by ring
            have h6 : 0 ≤ δ * (t / (1 - v z + t) ^ 2) := by positivity
            linarith
          · push_neg at hd
            nlinarith
      _ = ENNReal.ofReal (|Mx| / η ^ 2 * t) * ∫⁻ _z in K, (1 : ENNReal) ∂ν +
            ENNReal.ofReal δ * ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2) ∂ν := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (|Mx| / η ^ 2 * t) * C + ENNReal.ofReal δ * C := by
          gcongr
          refine (hmap _ hf).trans ?_
          calc _ ≤ C * 1 := by gcongr; exact lintegral_concKernel_le_one ht
            _ = C := mul_one C
      _ = _ := by
          rw [ENNReal.ofReal_add hδ.le hB]; ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hT : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x * C) (nhds 0) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal x) (nhds 0) (nhds 0) := by
      simpa using ENNReal.continuous_ofReal.tendsto 0
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)
  have hev := hT.eventually (gt_mem_nhds hε)
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨B, hB⟩ := key (r / 2) (by positivity)
  have hT2 : Filter.Tendsto (fun t : ℝ => r / 2 + B * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (r / 2)) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    have : Continuous (fun t : ℝ => r / 2 + B * t) := by fun_prop
    simpa using this.tendsto 0
  have hmem : Metric.ball (0 : ℝ) r ∈ nhds (r / 2) := by
    apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  filter_upwards [hT2.eventually hmem, self_mem_nhdsWithin] with t h1 h2
  exact (hB t h2).trans (hrb h1).le

end GlobalTheory
