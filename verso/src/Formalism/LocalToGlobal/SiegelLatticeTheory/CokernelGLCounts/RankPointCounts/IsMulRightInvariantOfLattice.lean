import Mathlib

noncomputable section

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.CovariantRepresentation

section Lattice

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

def lcount (Γ : Subgroup H) (K : Set H) (x : H) : ℝ≥0∞ := ∑' γ : Γ, K.indicator 1 ((γ : H) * x)

def lwt (Γ : Subgroup H) (K : Set H) (x : H) : ℝ≥0∞ := K.indicator 1 x * (lcount Γ K x)⁻¹

/- English proof (translation)
Establish `hK' : IsCompact ((fun y => y * x⁻¹) '' K)` using `hK.image (continuous_mul_const x⁻¹)`. Establish `h1` using `(Γ.tendsto_coe_cofinite_of_discrete (isDiscrete_iff_discreteTopology.mpr inferInstance)) hK'.compl_mem_cocompact`. Use `(Filter.mem_cofinite.1 h1).subset ?_` and prove the remaining obligations. Introduce `γ hγ`. Simplify using `only [Set.mem_compl_iff, Set.mem_preimage, not_not]`.

Conclude with `⟨(γ : H) * x, hγ, by simp⟩`.
-/
theorem finite_hits (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (x : H) :
    {γ : Γ | (γ : H) * x ∈ K}.Finite := by
  have hK' : IsCompact ((fun y => y * x⁻¹) '' K) := hK.image (continuous_mul_const x⁻¹)
  have h1 := (Γ.tendsto_coe_cofinite_of_discrete (isDiscrete_iff_discreteTopology.mpr inferInstance))
    hK'.compl_mem_cocompact
  refine (Filter.mem_cofinite.1 h1).subset ?_
  intro γ hγ
  simp only [Set.mem_compl_iff, Set.mem_preimage, not_not]
  exact ⟨(γ : H) * x, hγ, by simp⟩

/- English proof (translation)
Establish `hs` using `finite_hits Γ hK x`. Unfold `lcount`. Rewrite using `[tsum_eq_sum (s := hs.toFinset) ?_]`. Conclude with `ENNReal.sum_ne_top.2 fun γ _ => by`. Apply the tactic sequence `by_cases h : (γ : H) * x ∈ K <;> simp [Set.indicator, h]`.

Introduce `γ hγ`. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ`. Simplify using `[Set.indicator, hγ]`.
-/
theorem lcount_ne_top (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (x : H) :
    lcount Γ K x ≠ ∞ := by
  have hs := finite_hits Γ hK x
  unfold lcount
  rw [tsum_eq_sum (s := hs.toFinset) ?_]
  · exact ENNReal.sum_ne_top.2 fun γ _ => by
      by_cases h : (γ : H) * x ∈ K <;> simp [Set.indicator, h]
  · intro γ hγ
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
    simp [Set.indicator, hγ]

/- English proof (translation)
Take `⟨s, hs, hsx⟩` from `hcov x`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_lcount (Γ : Subgroup H) {K : Set H} (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (x : H) :
    1 ≤ lcount Γ K x := by
  obtain ⟨s, hs, hsx⟩ := hcov x
  calc (1 : ℝ≥0∞) = K.indicator 1 (((⟨s, hs⟩ : Γ) : H) * x) := by simp [hsx]
    _ ≤ lcount Γ K x := ENNReal.le_tsum (f := fun γ : Γ => K.indicator 1 ((γ : H) * x)) _

/- English proof (translation)
Unfold `lcount`. Use `(Equiv.mulRight δ).tsum_eq (fun γ : Γ => K.indicator (1 : H → ℝ≥0∞) ((γ : H) * x))` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
theorem lcount_mul (Γ : Subgroup H) (K : Set H) (δ : Γ) (x : H) :
    lcount Γ K ((δ : H) * x) = lcount Γ K x := by
  unfold lcount
  have := (Equiv.mulRight δ).tsum_eq (fun γ : Γ => K.indicator (1 : H → ℝ≥0∞) ((γ : H) * x))
  simpa [mul_assoc] using this

/- English proof (translation)
The claim follows from `Measurable.ennreal_tsum fun _ => ((measurable_one : Measurable (1 : H → ℝ≥0∞)).indicator hK.measurableSet).comp (measurable_const_mul _)`.
-/
theorem measurable_lcount (Γ : Subgroup H) [Countable Γ] {K : Set H} (hK : IsCompact K) :
    Measurable (lcount Γ K) :=
  Measurable.ennreal_tsum fun _ =>
    ((measurable_one : Measurable (1 : H → ℝ≥0∞)).indicator hK.measurableSet).comp (measurable_const_mul _)

/- English proof (translation)
The claim follows from `((measurable_one : Measurable (1 : H → ℝ≥0∞)).indicator hK.measurableSet).mul (measurable_lcount Γ hK).inv`.
-/
theorem measurable_lwt (Γ : Subgroup H) [Countable Γ] {K : Set H} (hK : IsCompact K) :
    Measurable (lwt Γ K) :=
  ((measurable_one : Measurable (1 : H → ℝ≥0∞)).indicator hK.measurableSet).mul (measurable_lcount Γ hK).inv

/- English proof (translation)
Unfold `lwt`. Repeatedly rewrite using `[lcount_mul]`. Rewrite using `[ENNReal.tsum_mul_right]`. Conclude with `ENNReal.mul_inv_cancel (zero_lt_one.trans_le (one_le_lcount Γ hcov x)).ne' (lcount_ne_top Γ hK x)`.
-/
theorem tsum_lwt (Γ : Subgroup H) [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K)
    (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (x : H) : ∑' γ : Γ, lwt Γ K ((γ : H) * x) = 1 := by
  unfold lwt
  simp_rw [lcount_mul]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_inv_cancel (zero_lt_one.trans_le (one_le_lcount Γ hcov x)).ne' (lcount_ne_top Γ hK x)

/- English proof (translation)
The claim follows from `mul_le_of_le_one_right (by positivity) (ENNReal.inv_le_one.2 (one_le_lcount Γ hcov x))`.
-/
theorem lwt_le (Γ : Subgroup H) {K : Set H} (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (x : H) :
    lwt Γ K x ≤ K.indicator 1 x :=
  mul_le_of_le_one_right (by positivity) (ENNReal.inv_le_one.2 (one_le_lcount Γ hcov x))

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[ENNReal.tsum_mul_left, hg1, mul_one]`. Use `_ = ∑' γ : Γ, ∫⁻ x, f x * g ((γ : H) * x) ∂μ := lintegral_tsum fun γ => (hf.mul (hg.comp (measurable_const_mul _))).aemeasurable`.

Use `_ = ∑' γ : Γ, ∫⁻ y, f ((γ : H)⁻¹ * y) * g y ∂μ := by`. Use `congr 1`. Use function extensionality and compare the values at `γ`. Use `lintegral_mul_left_eq_self (μ := μ) (fun y => f ((γ : H)⁻¹ * y) * g y) (γ : H)` as an intermediate fact. Simplify `this` using `only [inv_mul_cancel_left]`.

Use `_ = ∫⁻ y, ∑' γ : Γ, f ((γ : H)⁻¹ * y) * g y ∂μ := (lintegral_tsum fun γ => ((hf.comp (measurable_const_mul _)).mul hg).aemeasurable).symm`. Use `_ = ∫⁻ y, g y ∂μ := by`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[ENNReal.tsum_mul_right]`.

Use `(Equiv.inv Γ).tsum_eq (fun γ : Γ => f ((γ : H) * y))` as an intermediate fact. Simplify using `only [Equiv.inv_apply, Subgroup.coe_inv] at this`. Rewrite using `[this, hf1, one_mul]`.
-/
theorem lintegral_eq_of_tsum (μ : Measure H) [μ.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ]
    {f g : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, ∑' γ : Γ, f ((γ : H) * x) = 1) (hg1 : ∀ x, ∑' γ : Γ, g ((γ : H) * x) = 1) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ := by
  calc ∫⁻ x, f x ∂μ = ∫⁻ x, ∑' γ : Γ, f x * g ((γ : H) * x) ∂μ := by
        congr 1; funext x; rw [ENNReal.tsum_mul_left, hg1, mul_one]
    _ = ∑' γ : Γ, ∫⁻ x, f x * g ((γ : H) * x) ∂μ :=
        lintegral_tsum fun γ => (hf.mul (hg.comp (measurable_const_mul _))).aemeasurable
    _ = ∑' γ : Γ, ∫⁻ y, f ((γ : H)⁻¹ * y) * g y ∂μ := by
        congr 1; funext γ
        have := lintegral_mul_left_eq_self (μ := μ) (fun y => f ((γ : H)⁻¹ * y) * g y) (γ : H)
        simpa only [inv_mul_cancel_left] using this
    _ = ∫⁻ y, ∑' γ : Γ, f ((γ : H)⁻¹ * y) * g y ∂μ :=
        (lintegral_tsum fun γ => ((hf.comp (measurable_const_mul _)).mul hg).aemeasurable).symm
    _ = ∫⁻ y, g y ∂μ := by
        congr 1; funext y
        rw [ENNReal.tsum_mul_right]
        have := (Equiv.inv Γ).tsum_eq (fun γ : Γ => f ((γ : H) * y))
        simp only [Equiv.inv_apply, Subgroup.coe_inv] at this
        rw [this, hf1, one_mul]

/- English proof (translation)
Rewrite using `[← ENNReal.smul_def, modularCharacterFun_eq_haarScalarFactor μ g]`. Conclude with `isMulLeftInvariant_eq_smul (μ.map (· * g)) μ`.
-/
theorem map_mul_right_eq_modular (μ : Measure H) [IsHaarMeasure μ] (g : H) :
    μ.map (· * g) = ((modularCharacterFun g : ℝ≥0) : ℝ≥0∞) • μ := by
  rw [← ENNReal.smul_def, modularCharacterFun_eq_haarScalarFactor μ g]
  exact isMulLeftInvariant_eq_smul (μ.map (· * g)) μ

/- English proof (translation)
Use `set I := ∫⁻ x, lwt Γ K x ∂μ with hI`. Establish `hw` using `measurable_lwt Γ hK`. Establish `hItop : I ≠ ∞`. Use `ne_top_of_le_ne_top (hK.measure_lt_top (μ := μ)).ne ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hI0 : I ≠ 0`. Introduce `h0`. Establish `huniv : μ univ = ∑' γ : Γ, I`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[tsum_lwt Γ hK hcov x]`. Use `_ = ∑' γ : Γ, ∫⁻ x, lwt Γ K ((γ : H) * x) ∂μ := lintegral_tsum fun γ => (hw.comp (measurable_const_mul _)).aemeasurable`. Use `_ = ∑' γ : Γ, I := by`. Use `congr 1`.

Use function extensionality and compare the values at `γ`. Conclude with `lintegral_mul_left_eq_self _ _`. Rewrite `huniv` using `[h0, tsum_zero, Measure.measure_univ_eq_zero]`. Conclude with `NeZero.ne μ huniv`. Establish `hshift : ∫⁻ x, lwt Γ K (x * δ) ∂μ = I` using `(lintegral_eq_of_tsum μ Γ (hw.comp (measurable_mul_const δ)) hw (fun x => by simpa [mul_assoc] using tsum_lwt Γ hK hcov (x * δ)) (tsum_lwt Γ hK hcov)).trans rfl`.

Establish `hmap : ∫⁻ x, lwt Γ K (x * δ) ∂μ = (modularCharacterFun δ : ℝ≥0∞) * I`. Rewrite using `[← lintegral_map hw (measurable_mul_const δ), map_mul_right_eq_modular μ δ, lintegral_smul_measure]`. Apply the tactic sequence `all_goals first | rfl | simp [hI]`. Establish `: (modularCharacterFun δ : ℝ≥0∞) * I = 1 * I` using `by rw [← hmap, hshift, one_mul]`. Conclude with `ENNReal.coe_eq_one.1 ((ENNReal.mul_left_inj hI0 hItop).1 this)`.
-/
theorem modular_eq_one_of_mem (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K)
    {δ : H} (hδ : δ ∈ Γ) : modularCharacterFun δ = 1 := by
  set I := ∫⁻ x, lwt Γ K x ∂μ with hI
  have hw := measurable_lwt Γ hK
  have hItop : I ≠ ∞ := by
    refine ne_top_of_le_ne_top (hK.measure_lt_top (μ := μ)).ne ?_
    calc I ≤ ∫⁻ x, K.indicator 1 x ∂μ := lintegral_mono fun x => lwt_le Γ hcov x
      _ = μ K := lintegral_indicator_one hK.measurableSet
  have hI0 : I ≠ 0 := by
    intro h0
    have huniv : μ univ = ∑' γ : Γ, I := by
      calc μ univ = ∫⁻ _x, 1 ∂μ := (lintegral_one).symm
        _ = ∫⁻ x, ∑' γ : Γ, lwt Γ K ((γ : H) * x) ∂μ := by
            congr 1; funext x; rw [tsum_lwt Γ hK hcov x]
        _ = ∑' γ : Γ, ∫⁻ x, lwt Γ K ((γ : H) * x) ∂μ :=
            lintegral_tsum fun γ => (hw.comp (measurable_const_mul _)).aemeasurable
        _ = ∑' γ : Γ, I := by
            congr 1; funext γ; exact lintegral_mul_left_eq_self _ _
    rw [h0, tsum_zero, Measure.measure_univ_eq_zero] at huniv
    exact NeZero.ne μ huniv
  have hshift : ∫⁻ x, lwt Γ K (x * δ) ∂μ = I :=
    (lintegral_eq_of_tsum μ Γ (hw.comp (measurable_mul_const δ)) hw
      (fun x => by simpa [mul_assoc] using tsum_lwt Γ hK hcov (x * δ)) (tsum_lwt Γ hK hcov)).trans rfl
  have hmap : ∫⁻ x, lwt Γ K (x * δ) ∂μ = (modularCharacterFun δ : ℝ≥0∞) * I := by
    rw [← lintegral_map hw (measurable_mul_const δ), map_mul_right_eq_modular μ δ, lintegral_smul_measure]
    all_goals first | rfl | simp [hI]
  have : (modularCharacterFun δ : ℝ≥0∞) * I = 1 * I := by rw [← hmap, hshift, one_mul]
  exact ENNReal.coe_eq_one.1 ((ENNReal.mul_left_inj hI0 hItop).1 this)

/- English proof (translation)
Take `⟨V, hV, hV1⟩` from `exists_compact_mem_nhds (1 : H)`. Establish `hVpos : 0 < μ V` using `measure_pos_of_mem_nhds μ hV1`. Establish `hB : μ (V * K⁻¹) ≠ ∞` using `(hV.mul hK.inv).measure_lt_top.ne`. Use `set b : ℝ≥0 := (μ (V * K⁻¹) / μ V).toNNReal`. Establish `hbd : ∀ r : H, modularCharacterFun r ≤ b`.

Introduce `r`. Take `⟨s, hs, hsr⟩` from `hcov r`. Establish `hmul : modularCharacterFun r = modularCharacterFun (s * r)`. Rewrite using `[modularCharacterFun_map_mul, modular_eq_one_of_mem μ Γ hK hcov hs, one_mul]`. Rewrite using `[hmul]`.

Establish `h1 : (modularCharacterFun (s * r) : ℝ≥0∞) * μ V ≤ μ (V * K⁻¹)`. Establish `e` using `congrArg (fun m : Measure H => m V) (map_mul_right_eq_modular μ (s * r))`. Simplify using `only [Measure.smul_apply, smul_eq_mul] at e`. Rewrite using `[← e, Measure.map_apply (measurable_mul_const _) hV.measurableSet]`. Use `measure_mono fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : x * (s * r) ∈ V` using `hx`. Establish `: x = (x * (s * r)) * (s * r)⁻¹` using `by group`. Rewrite using `[this]`. Conclude with `Set.mul_mem_mul hx' (Set.inv_mem_inv.2 hsr)`. Establish `h2 : (modularCharacterFun (s * r) : ℝ≥0∞) ≤ μ (V * K⁻¹) / μ V` using `(ENNReal.le_div_iff_mul_le (Or.inl hVpos.ne') (Or.inr hB)).2 h1`.

Establish `hne : μ (V * K⁻¹) / μ V ≠ ∞` using `ENNReal.div_ne_top hB hVpos.ne'`. Conclude with `ENNReal.coe_le_coe.1 (h2.trans_eq (ENNReal.coe_toNNReal hne).symm)`. Establish `hle : ∀ r : H, modularCharacterFun r ≤ 1`. Introduce `r`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt b h`. Use `hbd (r ^ n)` as an intermediate fact. Establish `e : modularCharacterFun (r ^ n) = modularCharacterFun r ^ n` using `map_pow (modularCharacter (G := H)) r n`. Rewrite `this` using `[e]`.

Conclude with `absurd this (not_le.2 hn)`. Establish `hone : modularCharacterFun g = 1`. Use `le_antisymm (hle g) ?_` and prove the remaining obligations. Establish `e : modularCharacterFun g * modularCharacterFun g⁻¹ = 1`. Rewrite using `[← modularCharacterFun_map_mul, mul_inv_cancel, modularCharacterFun_map_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul_right_eq_modular μ g, hone, ENNReal.coe_one, one_smul]`.
-/
theorem haar_map_mul_right_of_lattice (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (g : H) :
    μ.map (· * g) = μ := by

  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : H)
  have hVpos : 0 < μ V := measure_pos_of_mem_nhds μ hV1
  have hB : μ (V * K⁻¹) ≠ ∞ := (hV.mul hK.inv).measure_lt_top.ne

  set b : ℝ≥0 := (μ (V * K⁻¹) / μ V).toNNReal
  have hbd : ∀ r : H, modularCharacterFun r ≤ b := by
    intro r
    obtain ⟨s, hs, hsr⟩ := hcov r
    have hmul : modularCharacterFun r = modularCharacterFun (s * r) := by
      rw [modularCharacterFun_map_mul, modular_eq_one_of_mem μ Γ hK hcov hs, one_mul]
    rw [hmul]
    have h1 : (modularCharacterFun (s * r) : ℝ≥0∞) * μ V ≤ μ (V * K⁻¹) := by
      have e := congrArg (fun m : Measure H => m V) (map_mul_right_eq_modular μ (s * r))
      simp only [Measure.smul_apply, smul_eq_mul] at e
      rw [← e, Measure.map_apply (measurable_mul_const _) hV.measurableSet]
      refine measure_mono fun x hx => ?_
      have hx' : x * (s * r) ∈ V := hx
      have : x = (x * (s * r)) * (s * r)⁻¹ := by group
      rw [this]
      exact Set.mul_mem_mul hx' (Set.inv_mem_inv.2 hsr)
    have h2 : (modularCharacterFun (s * r) : ℝ≥0∞) ≤ μ (V * K⁻¹) / μ V :=
      (ENNReal.le_div_iff_mul_le (Or.inl hVpos.ne') (Or.inr hB)).2 h1
    have hne : μ (V * K⁻¹) / μ V ≠ ∞ := ENNReal.div_ne_top hB hVpos.ne'
    exact ENNReal.coe_le_coe.1 (h2.trans_eq (ENNReal.coe_toNNReal hne).symm)
  have hle : ∀ r : H, modularCharacterFun r ≤ 1 := by
    intro r
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b h
    have := hbd (r ^ n)
    have e : modularCharacterFun (r ^ n) = modularCharacterFun r ^ n :=
      map_pow (modularCharacter (G := H)) r n
    rw [e] at this
    exact absurd this (not_le.2 hn)
  have hone : modularCharacterFun g = 1 := by
    refine le_antisymm (hle g) ?_
    have e : modularCharacterFun g * modularCharacterFun g⁻¹ = 1 := by
      rw [← modularCharacterFun_map_mul, mul_inv_cancel, modularCharacterFun_map_one]
    calc (1 : ℝ≥0) = modularCharacterFun g * modularCharacterFun g⁻¹ := e.symm
      _ ≤ modularCharacterFun g * 1 := by gcongr; exact hle g⁻¹
      _ = modularCharacterFun g := mul_one _
  rw [map_mul_right_eq_modular μ g, hone, ENNReal.coe_one, one_smul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun g => haar_map_mul_right_of_lattice μ Γ hK hcov g⟩`.
-/
theorem isMulRightInvariant_of_lattice (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) :
    μ.IsMulRightInvariant :=
  ⟨fun g => haar_map_mul_right_of_lattice μ Γ hK hcov g⟩

/- English proof (translation)
Use `haveI := isMulRightInvariant_of_lattice μ Γ hK hcov`. Set `c : ℝ≥0∞` to `haarScalarFactor μ.inv μ`. Establish `hc : μ.inv = c • μ` using `isMulLeftInvariant_eq_smul μ.inv μ`. Establish `h2 : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ`. Rewrite using `[← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]`.

Establish `μeq : μ = c ^ 2 • μ`. Rewrite `h2` using `[map_map continuous_inv.measurable continuous_inv.measurable]`. Simplify `h2` using `only [inv_involutive, Function.Involutive.comp_self, Measure.map_id]`. Take `⟨V, hV, hV1⟩` from `exists_compact_mem_nhds (1 : H)`. Establish `hVpos : 0 < μ V` using `measure_pos_of_mem_nhds μ hV1`.

Establish `e : c ^ 2 * μ V = 1 ^ 2 * μ V` using `by conv_rhs => rw [μeq]`. Simplify using the standard rewrite rules. Establish `e2 : c ^ 2 = 1 ^ 2` using `(ENNReal.mul_left_inj hVpos.ne' hV.measure_lt_top.ne).1 e`. Establish `e3 : c = 1` using `(ENNReal.pow_right_strictMono two_ne_zero).injective e2`. Express the relevant statement in the definitionally equal form `μ.inv = μ`.

Rewrite using `[hc, e3, one_smul]`.
-/
theorem haar_map_inv_of_lattice (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) :
    μ.map (fun x => x⁻¹) = μ := by
  haveI := isMulRightInvariant_of_lattice μ Γ hK hcov
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : H)
  have hVpos : 0 < μ V := measure_pos_of_mem_nhds μ hV1
  have e : c ^ 2 * μ V = 1 ^ 2 * μ V := by
    conv_rhs => rw [μeq]
    simp
  have e2 : c ^ 2 = 1 ^ 2 := (ENNReal.mul_left_inj hVpos.ne' hV.measure_lt_top.ne).1 e
  have e3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective e2
  change μ.inv = μ
  rw [hc, e3, one_smul]

/- English proof (translation)
Establish `e : (fun x => n⁻¹ * x * n) = (· * n) ∘ (n⁻¹ * ·)` using `rfl`. Rewrite using `[e, ← map_map (measurable_mul_const n) (measurable_const_mul n⁻¹), map_mul_left_eq_self μ n⁻¹, haar_map_mul_right_of_lattice μ Γ hK hcov n]`.
-/
theorem haar_map_conj_of_lattice (μ : Measure H) [IsHaarMeasure μ] (Γ : Subgroup H) [Countable Γ]
    [DiscreteTopology Γ] {K : Set H} (hK : IsCompact K) (hcov : ∀ x : H, ∃ s ∈ Γ, s * x ∈ K) (n : H) :
    μ.map (fun x => n⁻¹ * x * n) = μ := by
  have e : (fun x => n⁻¹ * x * n) = (· * n) ∘ (n⁻¹ * ·) := rfl
  rw [e, ← map_map (measurable_mul_const n) (measurable_const_mul n⁻¹), map_mul_left_eq_self μ n⁻¹,
    haar_map_mul_right_of_lattice μ Γ hK hcov n]

end Lattice

section Bounded

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/- English proof (translation)
Establish `hpow : ∀ n : ℕ, μ.map (f^[n]) = c ^ n • μ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Function.iterate_succ, ← map_map (hf.iterate n).measurable hf.measurable, hc, Measure.map_smul, ih, smul_smul, pow_succ']`. Establish `hVpos : 0 < μ V` using `measure_pos_of_mem_nhds μ hV1`. Establish `hLtop : μ L ≠ ∞` using `hL.measure_lt_top.ne`. Establish `hle : ∀ n : ℕ, μ V ≤ c ^ n * μ L`. Introduce `n`.

Establish `hcpt : IsCompact (f^[n] '' V)` using `hV.image (hf.iterate n)`. Establish `e` using `congrArg (fun m : Measure H => m (f^[n] '' V)) (hpow n)`. Simplify using `only [Measure.smul_apply, smul_eq_mul] at e`. Rewrite `e` using `[Measure.map_apply (hf.iterate n).measurable hcpt.measurableSet, Set.preimage_image_eq _ (hinj.iterate n)]`. Rewrite using `[e]`.

Use `gcongr`. Conclude with `hb n`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `ht : Tendsto (fun n : ℕ => c ^ n * μ L) atTop (𝓝 0)`.

Simplify using `using ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h) (Or.inr hLtop)`. Take `⟨n, hn⟩` from `(ht.eventually (gt_mem_nhds hVpos)).exists`. Conclude with `absurd (hle n) (not_le.2 hn)`.
-/
theorem one_le_of_iterate_bounded (μ : Measure H) [IsHaarMeasure μ] {f : H → H} (hf : Continuous f)
    (hinj : Function.Injective f) {c : ℝ≥0∞} (hc : μ.map f = c • μ) {V L : Set H} (hV : IsCompact V)
    (hV1 : V ∈ 𝓝 (1 : H)) (hL : IsCompact L) (hb : ∀ n : ℕ, f^[n] '' V ⊆ L) : 1 ≤ c := by
  have hpow : ∀ n : ℕ, μ.map (f^[n]) = c ^ n • μ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ, ← map_map (hf.iterate n).measurable hf.measurable, hc, Measure.map_smul,
        ih, smul_smul, pow_succ']
  have hVpos : 0 < μ V := measure_pos_of_mem_nhds μ hV1
  have hLtop : μ L ≠ ∞ := hL.measure_lt_top.ne
  have hle : ∀ n : ℕ, μ V ≤ c ^ n * μ L := by
    intro n
    have hcpt : IsCompact (f^[n] '' V) := hV.image (hf.iterate n)
    have e := congrArg (fun m : Measure H => m (f^[n] '' V)) (hpow n)
    simp only [Measure.smul_apply, smul_eq_mul] at e
    rw [Measure.map_apply (hf.iterate n).measurable hcpt.measurableSet,
      Set.preimage_image_eq _ (hinj.iterate n)] at e
    rw [e]
    gcongr
    exact hb n
  by_contra h
  push_neg at h
  have ht : Tendsto (fun n : ℕ => c ^ n * μ L) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h) (Or.inr hLtop)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hVpos)).exists
  exact absurd (hle n) (not_le.2 hn)

/- English proof (translation)
Establish `hc : μ.map α = (haarScalarFactor (μ.map α) μ : ℝ≥0∞) • μ`. Rewrite using `[← ENNReal.smul_def]`. Conclude with `isMulLeftInvariant_eq_smul _ μ`. Establish `hc' : μ.map α.symm = (haarScalarFactor (μ.map α.symm) μ : ℝ≥0∞) • μ`. Rewrite using `[← ENNReal.smul_def]`.

Conclude with `isMulLeftInvariant_eq_smul _ μ`. Use `set c : ℝ≥0∞ := (haarScalarFactor (μ.map α) μ : ℝ≥0∞)`. Use `set c' : ℝ≥0∞ := (haarScalarFactor (μ.map α.symm) μ : ℝ≥0∞)`. Establish `h1 : 1 ≤ c` using `one_le_of_iterate_bounded μ α.continuous α.injective hc hV hV1 hL fun n => (hb n).1`. Establish `h2 : 1 ≤ c'` using `one_le_of_iterate_bounded μ α.symm.continuous α.symm.injective hc' hV hV1 hL fun n => (hb n).2`.

Establish `hid : μ = (c * c') • μ`. Establish `e : μ.map (⇑α.symm ∘ ⇑α) = μ`. Establish `: (⇑α.symm ∘ ⇑α) = id` using `funext fun x => α.symm_apply_apply x`. Rewrite using `[this, Measure.map_id]`. Rewrite `e` using `[← map_map (show Measurable (⇑α.symm) from α.symm.continuous.measurable) (show Measurable (⇑α) from α.continuous.measurable), hc, Measure.map_smul, hc', smul_smul]`.

Conclude with `e.symm`. Take `⟨W, hW, hW1⟩` from `exists_compact_mem_nhds (1 : H)`. Establish `hWpos : 0 < μ W` using `measure_pos_of_mem_nhds μ hW1`. Establish `e : c * c' * μ W = 1 * μ W` using `by conv_rhs => rw [hid]`. Simplify using the standard rewrite rules.

Establish `hcc : c * c' = 1` using `(ENNReal.mul_left_inj hWpos.ne' hW.measure_lt_top.ne).1 e`. Establish `hc1 : c = 1` using `le_antisymm (by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc, hc1, one_smul]`.
-/
theorem haar_map_equiv_of_bounded (μ : Measure H) [IsHaarMeasure μ] (α : H ≃ₜ* H) {V L : Set H}
    (hV : IsCompact V) (hV1 : V ∈ 𝓝 (1 : H)) (hL : IsCompact L)
    (hb : ∀ n : ℕ, (⇑α)^[n] '' V ⊆ L ∧ (⇑α.symm)^[n] '' V ⊆ L) : μ.map α = μ := by
  have hc : μ.map α = (haarScalarFactor (μ.map α) μ : ℝ≥0∞) • μ := by
    rw [← ENNReal.smul_def]; exact isMulLeftInvariant_eq_smul _ μ
  have hc' : μ.map α.symm = (haarScalarFactor (μ.map α.symm) μ : ℝ≥0∞) • μ := by
    rw [← ENNReal.smul_def]; exact isMulLeftInvariant_eq_smul _ μ
  set c : ℝ≥0∞ := (haarScalarFactor (μ.map α) μ : ℝ≥0∞)
  set c' : ℝ≥0∞ := (haarScalarFactor (μ.map α.symm) μ : ℝ≥0∞)
  have h1 : 1 ≤ c := one_le_of_iterate_bounded μ α.continuous α.injective hc hV hV1 hL fun n => (hb n).1
  have h2 : 1 ≤ c' :=
    one_le_of_iterate_bounded μ α.symm.continuous α.symm.injective hc' hV hV1 hL fun n => (hb n).2
  have hid : μ = (c * c') • μ := by
    have e : μ.map (⇑α.symm ∘ ⇑α) = μ := by
      have : (⇑α.symm ∘ ⇑α) = id := funext fun x => α.symm_apply_apply x
      rw [this, Measure.map_id]
    rw [← map_map (show Measurable (⇑α.symm) from α.symm.continuous.measurable)
      (show Measurable (⇑α) from α.continuous.measurable), hc, Measure.map_smul, hc',
      smul_smul] at e
    exact e.symm
  obtain ⟨W, hW, hW1⟩ := exists_compact_mem_nhds (1 : H)
  have hWpos : 0 < μ W := measure_pos_of_mem_nhds μ hW1
  have e : c * c' * μ W = 1 * μ W := by
    conv_rhs => rw [hid]
    simp
  have hcc : c * c' = 1 := (ENNReal.mul_left_inj hWpos.ne' hW.measure_lt_top.ne).1 e
  have hc1 : c = 1 := le_antisymm (by
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * c' := by gcongr
      _ = 1 := hcc) h1
  rw [hc, hc1, one_smul]

end Bounded

end Formalism.L2.SG.CovariantRepresentation
