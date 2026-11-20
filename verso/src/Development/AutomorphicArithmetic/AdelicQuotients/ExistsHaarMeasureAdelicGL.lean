import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology Filter

/- English proof (translation)
Unfold `HaarEx`. Introduce `V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hR μ μi m hμ hμi hm S`. Use `haveI : ∀ v, (m v).IsHaarMeasure := hm`. Establish `cf : Continuous (prS q p S)`. Establish `h : ⇑(prS q p S) = fun g => (q g, fun v : S => p v g)` using `rfl`.

Rewrite using `[h]`. Conclude with `hR.cq.prodMk (continuous_pi fun v => hR.cp v)`. Establish `mf : Measurable (prS q p S)` using `cf.measurable`. Establish `hs : ∀ h : Gi × ∀ v : S, Gv v, ∃ u ∈ US p K S, prS q p S u = h`. Introduce and unpack `⟨gi, gv⟩`.

Take `⟨g, h1, h2⟩` from `hR.surj gi (fun v => if hv : v ∈ S then gv ⟨v, hv⟩ else 1) (by filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv`. Establish `hv' : v ∉ S` using `by simpa using hv`. Rewrite using `[dif_neg hv']`. Conclude with `one_mem _)`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v hv`. Rewrite using `[h2, dif_neg hv]`. Conclude with `one_mem _`. Rewrite using `[prS_apply, h1]`. Use `congr 1`.

Use function extensionality and compare the values at `v`. Rewrite using `[h2, dif_pos v.2]`. Take `⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (US p K S : Set G)).map (prS q p S)` from `⟨_, rfl⟩`. Use `haveI inv : ν.IsMulLeftInvariant := by`. Use `⟨fun h => ?_⟩` and prove the remaining obligations.

Take `⟨u, hu, rfl⟩` from `hs h`. Use extensionality with `A hA`. Establish `hA' : MeasurableSet ((fun x => prS q p S u * x) ⁻¹' A)` using `measurable_const_mul _ hA`. Rewrite using `[Measure.map_apply (measurable_const_mul _) hA, hν, Measure.map_apply mf hA', Measure.map_apply mf hA, Measure.restrict_apply (mf hA'), Measure.restrict_apply (mf hA)]`. Establish `hset : prS q p S ⁻¹' ((fun x => prS q p S u * x) ⁻¹' A) ∩ (US p K S : Set G) = (fun x => u * x) ⁻¹' (prS q p S ⁻¹' A ∩ (US p K S : Set G))`.

Use extensionality with `g`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe, Subgroup.mul_mem_cancel_left _ hu]`. Rewrite using `[hset, measure_preimage_mul]`. Use `haveI fin : IsFiniteMeasureOnCompacts ν := by`. Use `⟨fun D hD => ?_⟩` and prove the remaining obligations.

Rewrite using `[hν, Measure.map_apply mf hD.measurableSet, Measure.restrict_apply (mf hD.measurableSet)]`. Set `C : ∀ v, Set (Gv v)` to `fun v => if hv : v ∈ S then (fun h : Gi × ∀ v : S, Gv v => h.2 ⟨v, hv⟩) '' D else K v`. Establish `hC : ∀ v, IsCompact (C v)`. Introduce `v`. Distinguish the cases in `hv : v ∈ S`.

Simplify using `only [C, dif_pos hv]`. Conclude with `hD.image (by fun_prop)`. Simplify using `only [C, dif_neg hv]`. Conclude with `hR.cpt v`. Establish `hW` using `hR.prop (Prod.fst '' D) C (hD.image continuous_fst) hC (by filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv`.

Establish `hv' : v ∉ S` using `by simpa using hv`. Simplify using `only [C, dif_neg hv']`. Conclude with `subset_rfl)`. Use `lt_of_le_of_lt (measure_mono ?_) hW.measure_lt_top` and prove the remaining obligations. Introduce and unpack `g ⟨h1, h2⟩`.

Use `⟨⟨_, h1, rfl⟩, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [C, dif_pos hv]`. Conclude with `⟨_, h1, rfl⟩`. Simplify using `only [C, dif_neg hv]`.

Conclude with `h2 v hv`. Establish `e` using `Measure.isMulLeftInvariant_eq_smul ν (μi.prod (Measure.pi fun v : S => m v))`. Use `⟨Measure.haarScalarFactor ν (μi.prod (Measure.pi fun v : S => m v)), ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Rewrite `e` using `[h0, zero_smul]`.

Establish `h1 : ν Set.univ = 0` using `by rw [e]; rfl`. Rewrite `h1` using `[hν, Measure.map_apply mf MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]`. Conclude with `(hR.opnU S).measure_ne_zero μ ⟨1, one_mem _⟩ h1`. Unfold `Eul`. Rewrite using `[← hν]`.

Conclude with `e`.
-/
theorem UpperTheory.exists_haarMeasure_adelicGL :
    HaarEx := by
  unfold HaarEx
  intro V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hR μ μi m hμ hμi hm S
  classical
  haveI : ∀ v, (m v).IsHaarMeasure := hm
  have cf : Continuous (prS q p S) := by
    have h : ⇑(prS q p S) = fun g => (q g, fun v : S => p v g) := rfl
    rw [h]
    exact hR.cq.prodMk (continuous_pi fun v => hR.cp v)
  have mf : Measurable (prS q p S) := cf.measurable
  have hs : ∀ h : Gi × ∀ v : S, Gv v, ∃ u ∈ US p K S, prS q p S u = h := by
    rintro ⟨gi, gv⟩
    obtain ⟨g, h1, h2⟩ := hR.surj gi (fun v => if hv : v ∈ S then gv ⟨v, hv⟩ else 1) (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      rw [dif_neg hv']
      exact one_mem _)
    refine ⟨g, ?_, ?_⟩
    · intro v hv
      rw [h2, dif_neg hv]
      exact one_mem _
    · rw [prS_apply, h1]
      congr 1
      funext v
      rw [h2, dif_pos v.2]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (US p K S : Set G)).map (prS q p S) := ⟨_, rfl⟩
  haveI inv : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hs h
    ext A hA
    have hA' : MeasurableSet ((fun x => prS q p S u * x) ⁻¹' A) := measurable_const_mul _ hA
    rw [Measure.map_apply (measurable_const_mul _) hA, hν, Measure.map_apply mf hA',
      Measure.map_apply mf hA, Measure.restrict_apply (mf hA'), Measure.restrict_apply (mf hA)]
    have hset : prS q p S ⁻¹' ((fun x => prS q p S u * x) ⁻¹' A) ∩ (US p K S : Set G) =
        (fun x => u * x) ⁻¹' (prS q p S ⁻¹' A ∩ (US p K S : Set G)) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe,
        Subgroup.mul_mem_cancel_left _ hu]
    rw [hset, measure_preimage_mul]
  haveI fin : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun D hD => ?_⟩
    rw [hν, Measure.map_apply mf hD.measurableSet, Measure.restrict_apply (mf hD.measurableSet)]
    let C : ∀ v, Set (Gv v) := fun v =>
      if hv : v ∈ S then (fun h : Gi × ∀ v : S, Gv v => h.2 ⟨v, hv⟩) '' D else K v
    have hC : ∀ v, IsCompact (C v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [C, dif_pos hv]
        exact hD.image (by fun_prop)
      · simp only [C, dif_neg hv]
        exact hR.cpt v
    have hW := hR.prop (Prod.fst '' D) C (hD.image continuous_fst) hC (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      simp only [C, dif_neg hv']
      exact subset_rfl)
    refine lt_of_le_of_lt (measure_mono ?_) hW.measure_lt_top
    rintro g ⟨h1, h2⟩
    refine ⟨⟨_, h1, rfl⟩, fun v => ?_⟩
    by_cases hv : v ∈ S
    · simp only [C, dif_pos hv]
      exact ⟨_, h1, rfl⟩
    · simp only [C, dif_neg hv]
      exact h2 v hv
  have e := Measure.isMulLeftInvariant_eq_smul ν (μi.prod (Measure.pi fun v : S => m v))
  refine ⟨Measure.haarScalarFactor ν (μi.prod (Measure.pi fun v : S => m v)), ?_, ?_⟩
  · intro h0
    rw [h0, zero_smul] at e
    have h1 : ν Set.univ = 0 := by rw [e]; rfl
    rw [hν, Measure.map_apply mf MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ] at h1
    exact (hR.opnU S).measure_ne_zero μ ⟨1, one_mem _⟩ h1
  · unfold Eul
    rw [← hν]
    exact e
