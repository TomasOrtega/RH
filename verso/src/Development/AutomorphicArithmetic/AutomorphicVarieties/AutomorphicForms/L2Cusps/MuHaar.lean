import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.KernelIndexFullLattice

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Rewrite using `[splitEq_holds E a 1, detModule_centralSection ha]`. Establish `h1 : (0 : ℝ) < a` using `Nat.cast_pos.2 ha`. Establish `h2 : (0 : ℝ) < Module.finrank ℚ E` using `Nat.cast_pos.2 Module.finrank_pos`. Express the relevant statement in the definitionally equal form `(1 : ℝ) < Real.exp _`. Conclude with `Real.one_lt_exp_iff.2 (by positivity)`.
-/
private theorem one_lt_top (ha : 0 < a) : 1 < detModule E a (splitCentre E a 1) := by
  rw [splitEq_holds E a 1, detModule_centralSection ha]
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  change (1 : ℝ) < Real.exp _
  exact Real.one_lt_exp_iff.2 (by positivity)

/- English proof (translation)
The claim follows from `Set.eq_univ_of_forall fun _ => Or.inl rfl`.
-/
private theorem band_zero : band E 0 = Set.univ := Set.eq_univ_of_forall fun _ => Or.inl rfl

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [band, Set.mem_setOf_eq, ha.ne', false_or, Set.mem_preimage, Set.mem_Ico]`.
-/
private theorem band_pos (ha : 0 < a) :
    band E a = detModule E a ⁻¹' Set.Ico 1 (detModule E a (splitCentre E a 1)) := by
  ext g
  simp only [band, Set.mem_setOf_eq, ha.ne', false_or, Set.mem_preimage, Set.mem_Ico]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Rewrite using `[band_zero]`. Conclude with `MeasurableSet.univ`. Rewrite using `[band_pos ha]`. Establish `hc : Continuous fun g : GA E a => (detModule E a g : ℝ)` using `continuous_subtype_val.comp continuous_detModule`.

Conclude with `hc.measurable (measurableSet_Ico (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ)))`.
-/
private theorem measurableSet_band : MeasurableSet (band E a) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [band_zero]; exact MeasurableSet.univ
  · rw [band_pos ha]
    have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
      continuous_subtype_val.comp continuous_detModule
    exact hc.measurable (measurableSet_Ico (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ)))

/- English proof (translation)
The claim follows from `continuous_retractOne.measurable`.
-/
private theorem meas_retract : Measurable (retractOne : GA E a → G1 E a) := continuous_retractOne.measurable

/- English proof (translation)
Rewrite using `[muOne, Measure.map_apply meas_retract hA, Measure.restrict_apply (meas_retract hA)]`.
-/
private theorem muOne_apply (μ : Measure (GA E a)) {A : Set (G1 E a)} (hA : MeasurableSet A) :
    muOne μ A = μ (retractOne ⁻¹' A ∩ band E a) := by
  rw [muOne, Measure.map_apply meas_retract hA, Measure.restrict_apply (meas_retract hA)]

omit [IsTotallyComplex E] in
/- English proof (translation)
Use `ext1`. Rewrite using `[coe_retractOne, Subgroup.coe_mul, coe_retractOne, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul, mul_assoc]`.
-/
private theorem retract_mul_left (x : G1 E a) (g : GA E a) :
    retractOne ((x : GA E a) * g) = x * retractOne g := by
  ext1
  rw [coe_retractOne, Subgroup.coe_mul, coe_retractOne, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul,
    mul_assoc]

/- English proof (translation)
Simplify using `only [band, Set.mem_setOf_eq, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul]`.
-/
private theorem band_mul_left (x : G1 E a) (g : GA E a) : (x : GA E a) * g ∈ band E a ↔ g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul]

/- English proof (translation)
Use `Topology.IsInducing.subtypeVal.isCompact_iff.2 ?_` and prove the remaining obligations. Use `isCompact_Icc (a := (s : ℝ)) (b := (t : ℝ)) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `hy`. Introduce `hx`. Conclude with `⟨⟨x, s.2.trans_le hx.1⟩, hx, rfl⟩`.
-/
private theorem isCompact_posIcc (s t : {r : ℝ // 0 < r}) : IsCompact (Set.Icc s t) := by
  refine Topology.IsInducing.subtypeVal.isCompact_iff.2 ?_
  convert isCompact_Icc (a := (s : ℝ)) (b := (t : ℝ)) using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, s.2.trans_le hx.1⟩, hx, rfl⟩

end

/- English proof (translation)
Introduce `E _ _ _ a μ _`. Establish `h1 : (muOne μ).IsMulLeftInvariant`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Use extensionality with `A hA`. Establish `hm : Measurable fun y : G1 E a => x * y` using `measurable_const_mul x`.

Rewrite using `[Measure.map_apply hm hA, muOne_apply μ (hm hA), muOne_apply μ hA, ← measure_preimage_mul μ (x : GA E a) (retractOne ⁻¹' A ∩ band E a)]`. Use `congr 1`. Use extensionality with `g`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, retract_mul_left, band_mul_left]`. Establish `h2 : IsFiniteMeasureOnCompacts (muOne μ)`.

Use `⟨fun C hC => ?_⟩` and prove the remaining obligations. Rewrite using `[muOne_apply μ hC.measurableSet]`. Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Establish `: Subsingleton (GA E 0)` using `⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩`. Conclude with `(Set.toFinite _).isCompact.measure_lt_top`.

Establish `hc : Continuous fun p : G1 E a × {r : ℝ // 0 < r} => (p.1 : GA E a) * centralSection E a p.2` using `(continuous_subtype_val.comp continuous_fst).mul (continuous_centralSection.comp continuous_snd)`. Use `lt_of_le_of_lt (measure_mono ?_) ((hC.prod (isCompact_posIcc 1 (detModule E a (splitCentre E a 1)))).image hc).measure_lt_top` and prove the remaining obligations. Introduce and unpack `g ⟨hg, hb⟩`. Rewrite `hb` using `[band_pos ha]`. Use `⟨(retractOne g, detModule E a g), ⟨hg, hb.1, hb.2.le⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(retractOne g : GA E a) * centralSection E a (detModule E a g) = g`. Rewrite using `[coe_retractOne, inv_mul_cancel_right]`. Establish `h3 : (muOne μ).IsOpenPosMeasure`. Use `⟨fun U hU hne => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hne`.

Establish `hO : IsOpen (retractOne ⁻¹' U : Set (GA E a))` using `hU.preimage continuous_retractOne`. Rewrite using `[muOne_apply μ hU.measurableSet]`. Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Establish `: Subsingleton (GA E 0)` using `⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩`. Rewrite using `[band_zero, Set.inter_univ]`.

Use `hO.measure_ne_zero μ ⟨1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `retractOne _ ∈ U`. Rewrite using `[Subsingleton.elim (retractOne _) x]` and apply the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨s, hs1, hs2⟩ : ∃ s : {r : ℝ // 0 < r}, 1 < s ∧ s < detModule E a (splitCentre E a 1) := by`. Take `⟨s, h1, h2⟩` from `exists_between (show (1 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) from one_lt_top ha)`.

Conclude with `⟨⟨s, one_pos.trans h1⟩, h1, h2⟩`. Establish `hc : Continuous fun g : GA E a => (detModule E a g : ℝ)` using `continuous_subtype_val.comp continuous_detModule`. Establish `hI : IsOpen (detModule E a ⁻¹' Set.Ioo 1 (detModule E a (splitCentre E a 1)) : Set (GA E a))` using `(isOpen_Ioo (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ))).preimage hc`. Establish `hd : detModule E a ((x : GA E a) * centralSection E a s) = s`. Rewrite using `[map_mul, (mem_normOneGL_iff_detModule).1 x.2, detModule_centralSection ha, one_mul]`.

Establish `hr : retractOne ((x : GA E a) * centralSection E a s) = x` using `by ext1`. Rewrite using `[coe_retractOne, hd, mul_inv_cancel_right]`. Establish `hp` using `(hO.inter hI).measure_ne_zero μ ⟨(x : GA E a) * centralSection E a s, by`. Rewrite using `[Set.mem_preimage, hr]; exact hx, by rw [Set.mem_preimage, hd]; exact ⟨hs1, hs2⟩⟩`. Introduce `h0`.

Use `hp (measure_mono_null ?_ h0)` and prove the remaining obligations. Rewrite using `[band_pos ha]`. Conclude with `Set.inter_subset_inter_right _ (Set.preimage_mono Set.Ioo_subset_Ico_self)`. Conclude with `{}`.
-/
theorem UpperTheory.V.KernelIndexFullLattice.muHaar_holds :
    UpperTheory.V.KernelIndexFullLattice.MuHaar := by
  intro E _ _ _ a μ _
  have h1 : (muOne μ).IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    ext A hA
    have hm : Measurable fun y : G1 E a => x * y := measurable_const_mul x
    rw [Measure.map_apply hm hA, muOne_apply μ (hm hA), muOne_apply μ hA,
      ← measure_preimage_mul μ (x : GA E a) (retractOne ⁻¹' A ∩ band E a)]
    congr 1
    ext g
    simp only [Set.mem_inter_iff, Set.mem_preimage, retract_mul_left, band_mul_left]
  have h2 : IsFiniteMeasureOnCompacts (muOne μ) := by
    refine ⟨fun C hC => ?_⟩
    rw [muOne_apply μ hC.measurableSet]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
      exact (Set.toFinite _).isCompact.measure_lt_top
    · have hc : Continuous fun p : G1 E a × {r : ℝ // 0 < r} => (p.1 : GA E a) * centralSection E a p.2 :=
        (continuous_subtype_val.comp continuous_fst).mul (continuous_centralSection.comp continuous_snd)
      refine lt_of_le_of_lt (measure_mono ?_)
        ((hC.prod (isCompact_posIcc 1 (detModule E a (splitCentre E a 1)))).image hc).measure_lt_top
      rintro g ⟨hg, hb⟩
      rw [band_pos ha] at hb
      refine ⟨(retractOne g, detModule E a g), ⟨hg, hb.1, hb.2.le⟩, ?_⟩
      change (retractOne g : GA E a) * centralSection E a (detModule E a g) = g
      rw [coe_retractOne, inv_mul_cancel_right]
  have h3 : (muOne μ).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    obtain ⟨x, hx⟩ := hne
    have hO : IsOpen (retractOne ⁻¹' U : Set (GA E a)) := hU.preimage continuous_retractOne
    rw [muOne_apply μ hU.measurableSet]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
      rw [band_zero, Set.inter_univ]
      refine hO.measure_ne_zero μ ⟨1, ?_⟩
      change retractOne _ ∈ U
      rwa [Subsingleton.elim (retractOne _) x]
    · obtain ⟨s, hs1, hs2⟩ : ∃ s : {r : ℝ // 0 < r}, 1 < s ∧ s < detModule E a (splitCentre E a 1) := by
        obtain ⟨s, h1, h2⟩ := exists_between (show (1 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) from one_lt_top ha)
        exact ⟨⟨s, one_pos.trans h1⟩, h1, h2⟩
      have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
        continuous_subtype_val.comp continuous_detModule
      have hI : IsOpen (detModule E a ⁻¹' Set.Ioo 1 (detModule E a (splitCentre E a 1)) : Set (GA E a)) :=
        (isOpen_Ioo (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ))).preimage hc
      have hd : detModule E a ((x : GA E a) * centralSection E a s) = s := by
        rw [map_mul, (mem_normOneGL_iff_detModule).1 x.2, detModule_centralSection ha, one_mul]
      have hr : retractOne ((x : GA E a) * centralSection E a s) = x := by
        ext1
        rw [coe_retractOne, hd, mul_inv_cancel_right]
      have hp := (hO.inter hI).measure_ne_zero μ ⟨(x : GA E a) * centralSection E a s, by
        rw [Set.mem_preimage, hr]; exact hx, by rw [Set.mem_preimage, hd]; exact ⟨hs1, hs2⟩⟩
      intro h0
      refine hp (measure_mono_null ?_ h0)
      rw [band_pos ha]
      exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.Ioo_subset_Ico_self)
  exact {}
