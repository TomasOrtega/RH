import Mathlib

noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal NNReal

namespace PI.NMeasInv.UnitaryGroupMassFormula

section Abs

attribute [local instance] Classical.propDecidable

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

def HaarOn (N : Subgroup G) (μ : Measure G) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ (N : Set G)ᶜ = 0 ∧ ∀ s ∈ N, μ.map (fun x => s * x) = μ

/- English proof (translation)
Establish `hemb : MeasurableEmbedding ((↑) : H → G)` using `MeasurableEmbedding.subtype_coe hH.measurableSet`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hemb.measurable hs, hemb.comap_apply, Set.image_preimage_eq_inter_range]`. Establish `hr : Set.range ((↑) : H → G) = (H : Set G)` using `by ext x; simp`. Rewrite using `[hr]`.

Establish `h1` using `measure_inter_add_diff (μ := μ) s hH.measurableSet`. Establish `h2 : μ (s \ (H : Set G)) = 0` using `measure_mono_null (fun x hx => hx.2) hc`. Rewrite `h1` using `[h2, add_zero]`. Conclude with `h1`.
-/
theorem map_comap_subgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G)
    (hc : μ (H : Set G)ᶜ = 0) : (μ.comap ((↑) : H → G)).map ((↑) : H → G) = μ := by
  have hemb : MeasurableEmbedding ((↑) : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  ext s hs
  rw [Measure.map_apply hemb.measurable hs, hemb.comap_apply, Set.image_preimage_eq_inter_range]
  have hr : Set.range ((↑) : H → G) = (H : Set G) := by ext x; simp
  rw [hr]
  have h1 := measure_inter_add_diff (μ := μ) s hH.measurableSet
  have h2 : μ (s \ (H : Set G)) = 0 := measure_mono_null (fun x hx => hx.2) hc
  rw [h2, add_zero] at h1
  exact h1

/- English proof (translation)
Establish `hemb : MeasurableEmbedding (Subtype.val : S → G)` using `MeasurableEmbedding.subtype_coe hS.measurableSet`. Establish `hmc : (ν.comap (Subtype.val : S → G)).map Subtype.val = ν` using `map_comap_subgroup S hS ν hνc`. Use `⟨fun s => ?_⟩` and prove the remaining obligations. Establish `h1 : ((ν.comap (Subtype.val : S → G)).map (fun x : S => s * x)).map Subtype.val = ν`. Rewrite using `[Measure.map_map hemb.measurable (measurable_const_mul s)]`.

Establish `hc : (Subtype.val ∘ fun x : S => s * x) = (fun y : G => (s : G) * y) ∘ Subtype.val`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[hc, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmc]`. Conclude with `hνi s s.2`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem abs_inv_lemma (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G)
    (hνc : ν (S : Set G)ᶜ = 0) (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant := by
  have hemb : MeasurableEmbedding (Subtype.val : S → G) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hmc : (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := map_comap_subgroup S hS ν hνc
  refine ⟨fun s => ?_⟩
  have h1 : ((ν.comap (Subtype.val : S → G)).map (fun x : S => s * x)).map Subtype.val = ν := by
    rw [Measure.map_map hemb.measurable (measurable_const_mul s)]
    have hc : (Subtype.val ∘ fun x : S => s * x) = (fun y : G => (s : G) * y) ∘ Subtype.val := by
      funext x; simp
    rw [hc, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmc]
    exact hνi s s.2
  calc Measure.map (fun x : S => s * x) (ν.comap Subtype.val)
      = ((Measure.map (fun x : S => s * x) (ν.comap Subtype.val)).map Subtype.val).comap
          Subtype.val := (hemb.comap_map _).symm
    _ = ν.comap Subtype.val := by rw [h1]

/- English proof (translation)
Use `haveI : SecondCountableTopology S := inferInstanceAs (SecondCountableTopology (S : Set G))`. Take `⟨K, hK, hK1⟩` from `exists_compact_mem_nhds (1 : S)`. Establish `hKpos : 0 < (haar : Measure S) K` using `lt_of_lt_of_le (isOpen_interior.measure_pos haar ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩) (measure_mono interior_subset)`. Establish `hKtop : (haar : Measure S) K ≠ ⊤` using `hK.measure_lt_top.ne`. Establish `heq` using `measure_eq_div_smul (s := K) la (haar : Measure S) hKpos.ne' hKtop`.

Use `⟨la K / haar K, ?_, ?_, heq⟩` and prove the remaining obligations. Introduce `hc`. Rewrite `heq` using `[hc, zero_smul]`. Conclude with `h0 heq`. Introduce `hc`.

Rewrite `heq` using `[hc]`. Establish `hsp : ∀ i, (haar : Measure S) (spanningSets la i) = 0`. Introduce `i`. Establish `h1 : ((⊤ : ℝ≥0∞) • (haar : Measure S)) (spanningSets la i) < ⊤`. Rewrite using `[← heq]`.

Conclude with `measure_spanningSets_lt_top la i`. Rewrite `h1` using `[Measure.smul_apply, smul_eq_mul]`. Assume the negation of the conclusion as `hne`. Rewrite `h1` using `[ENNReal.top_mul hne]`. Conclude with `lt_irrefl _ h1`.

Establish `hu : (haar : Measure S) Set.univ = 0`. Rewrite using `[← iUnion_spanningSets la]`. Conclude with `measure_iUnion_null hsp`. Conclude with `(isOpen_univ.measure_pos haar ⟨1, trivial⟩).ne' hu`.
-/
private theorem abs_scal_lemma_2 (S : Subgroup G) [LocallyCompactSpace S] (la : Measure S)
    [SigmaFinite la] [la.IsMulLeftInvariant] (h0 : la ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ la = c • (haar : Measure S) := by
  haveI : SecondCountableTopology S := inferInstanceAs (SecondCountableTopology (S : Set G))
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : S)
  have hKpos : 0 < (haar : Measure S) K :=
    lt_of_lt_of_le (isOpen_interior.measure_pos haar ⟨1, mem_interior_iff_mem_nhds.mpr hK1⟩)
      (measure_mono interior_subset)
  have hKtop : (haar : Measure S) K ≠ ⊤ := hK.measure_lt_top.ne
  have heq := measure_eq_div_smul (s := K) la (haar : Measure S) hKpos.ne' hKtop
  refine ⟨la K / haar K, ?_, ?_, heq⟩
  · intro hc; rw [hc, zero_smul] at heq; exact h0 heq
  · intro hc
    rw [hc] at heq
    have hsp : ∀ i, (haar : Measure S) (spanningSets la i) = 0 := by
      intro i
      have h1 : ((⊤ : ℝ≥0∞) • (haar : Measure S)) (spanningSets la i) < ⊤ := by
        rw [← heq]; exact measure_spanningSets_lt_top la i
      rw [Measure.smul_apply, smul_eq_mul] at h1
      by_contra hne
      rw [ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have hu : (haar : Measure S) Set.univ = 0 := by
      rw [← iUnion_spanningSets la]; exact measure_iUnion_null hsp
    exact (isOpen_univ.measure_pos haar ⟨1, trivial⟩).ne' hu

/- English proof (translation)
Use `haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Take `⟨hσ, h0, hc, hi⟩` from `hμ`. Establish `hemb : MeasurableEmbedding (Subtype.val : H → G)` using `MeasurableEmbedding.subtype_coe hH.measurableSet`. Establish `hmc` using `map_comap_subgroup H hH μ hc`. Use `haveI := abs_inv_lemma H hH μ hc hi`.

Use `haveI : SigmaFinite (μ.comap (Subtype.val : H → G)) := SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmc]; exact hσ)`. Establish `hne : μ.comap (Subtype.val : H → G) ≠ 0`. Introduce `h`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← hmc, h, Measure.map_zero]`.

Take `⟨c, hc0, hct, hceq⟩` from `abs_scal_lemma_2 H (μ.comap (Subtype.val : H → G)) hne`. Establish `hμeq : μ = c • (haar : Measure H).map Subtype.val`. Rewrite using `[← hmc, hceq, Measure.map_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `K hK`.

Rewrite using `[hμeq, Measure.smul_apply, Measure.map_apply hemb.measurable hK.isClosed.measurableSet, smul_eq_mul]`. Conclude with `ENNReal.mul_lt_top hct.lt_top ((hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top)`. Introduce `U hU hne'`. Rewrite using `[hμeq, Measure.smul_apply, Measure.map_apply hemb.measurable hU.measurableSet, smul_eq_mul]`. Take `⟨x, hxU, hxH⟩` from `hne'`.

Establish `hpos : 0 < (haar : Measure H) (Subtype.val ⁻¹' U)` using `(hU.preimage continuous_subtype_val).measure_pos haar ⟨⟨x, hxH⟩, hxU⟩`. Conclude with `ENNReal.mul_pos hc0 hpos.ne'`.
-/
theorem haarOn_props (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G) (hμ : HaarOn H μ) :
    (∀ K : Set G, IsCompact K → μ K < ⊤) ∧
      ∀ U : Set G, IsOpen U → (U ∩ (H : Set G)).Nonempty → 0 < μ U := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨hσ, h0, hc, hi⟩ := hμ
  have hemb : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hH.measurableSet
  have hmc := map_comap_subgroup H hH μ hc
  haveI := abs_inv_lemma H hH μ hc hi
  haveI : SigmaFinite (μ.comap (Subtype.val : H → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmc]; exact hσ)
  have hne : μ.comap (Subtype.val : H → G) ≠ 0 := by
    intro h; apply h0; rw [← hmc, h, Measure.map_zero]
  obtain ⟨c, hc0, hct, hceq⟩ := abs_scal_lemma_2 H (μ.comap (Subtype.val : H → G)) hne
  have hμeq : μ = c • (haar : Measure H).map Subtype.val := by
    rw [← hmc, hceq, Measure.map_smul]
  constructor
  · intro K hK
    rw [hμeq, Measure.smul_apply, Measure.map_apply hemb.measurable hK.isClosed.measurableSet,
      smul_eq_mul]
    exact ENNReal.mul_lt_top hct.lt_top
      ((hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top)
  · intro U hU hne'
    rw [hμeq, Measure.smul_apply, Measure.map_apply hemb.measurable hU.measurableSet, smul_eq_mul]
    obtain ⟨x, hxU, hxH⟩ := hne'
    have hpos : 0 < (haar : Measure H) (Subtype.val ⁻¹' U) :=
      (hU.preimage continuous_subtype_val).measure_pos haar ⟨⟨x, hxH⟩, hxU⟩
    exact ENNReal.mul_pos hc0 hpos.ne'

/- English proof (translation)
Establish `hemb : MeasurableEmbedding (Subtype.val : S → G)` using `MeasurableEmbedding.subtype_coe hS.measurableSet`. Use `haveI := hνf`. Use `⟨abs_inv_lemma S hS ν hνc hνi, ⟨fun K hK => ?_⟩, map_comap_subgroup S hS ν hνc⟩` and prove the remaining obligations. Rewrite using `[hemb.comap_apply]`. Conclude with `(hK.image continuous_subtype_val).measure_lt_top`.
-/
theorem pull (S : Subgroup G) (hS : IsClosed (S : Set G)) (ν : Measure G) (hνc : ν (S : Set G)ᶜ = 0)
    (hνi : ∀ s ∈ S, ν.map (fun x => s * x) = ν) (hνf : IsFiniteMeasureOnCompacts ν) :
    (ν.comap (Subtype.val : S → G)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (ν.comap (Subtype.val : S → G)) ∧
      (ν.comap (Subtype.val : S → G)).map Subtype.val = ν := by
  have hemb : MeasurableEmbedding (Subtype.val : S → G) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  haveI := hνf
  refine ⟨abs_inv_lemma S hS ν hνc hνi, ⟨fun K hK => ?_⟩, map_comap_subgroup S hS ν hνc⟩
  rw [hemb.comap_apply]
  exact (hK.image continuous_subtype_val).measure_lt_top

/- English proof (translation)
Use `haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology S := inferInstanceAs (SecondCountableTopology (S : Set G))`. Take `⟨hμL, hμF, hμM⟩` from `pull S hS μ hμc hμi hμf`. Take `⟨hmL, hmF, hmM⟩` from `pull S hS m hmc hmi hmf`. Use `haveI := hμL`.

Use `haveI := hμF`. Use `haveI := hmL`. Use `haveI := hmF`. Take `⟨a, ea⟩ : ∃ a : ℝ≥0, μ.comap (Subtype.val : S → G) = a • (haar : Measure S)` from `⟨_, isMulLeftInvariant_eq_smul _ _⟩`. Take `⟨b, eb⟩ : ∃ b : ℝ≥0, m.comap (Subtype.val : S → G) = b • (haar : Measure S)` from `⟨_, isMulLeftInvariant_eq_smul _ _⟩`.

Establish `hμ' : μ = a • (haar : Measure S).map Subtype.val`. Combine the equalities or inequalities in the displayed calculation. Establish `hm' : m = b • (haar : Measure S).map Subtype.val`. Combine the equalities or inequalities in the displayed calculation. Establish `ha0 : a ≠ 0` using `by rintro rfl; apply hμ0; rw [hμ', zero_smul]`.

Use `⟨((b / a : ℝ≥0) : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩` and prove the remaining obligations. Rewrite using `[hm', hμ']`. Use extensionality with `s hs`. Simplify using `only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]`. Rewrite using `[← mul_assoc, ← ENNReal.coe_mul, div_mul_cancel₀ b ha0]`.
-/
theorem haar_unique (S : Subgroup G) (hS : IsClosed (S : Set G)) (μ m : Measure G) (hμ0 : μ ≠ 0)
    (hμc : μ (S : Set G)ᶜ = 0) (hμi : ∀ s ∈ S, μ.map (fun x => s * x) = μ) (hμf : IsFiniteMeasureOnCompacts μ)
    (hmc : m (S : Set G)ᶜ = 0) (hmi : ∀ s ∈ S, m.map (fun x => s * x) = m) (hmf : IsFiniteMeasureOnCompacts m) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ m = c • μ := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S := inferInstanceAs (SecondCountableTopology (S : Set G))
  obtain ⟨hμL, hμF, hμM⟩ := pull S hS μ hμc hμi hμf
  obtain ⟨hmL, hmF, hmM⟩ := pull S hS m hmc hmi hmf
  haveI := hμL; haveI := hμF; haveI := hmL; haveI := hmF
  obtain ⟨a, ea⟩ : ∃ a : ℝ≥0, μ.comap (Subtype.val : S → G) = a • (haar : Measure S) :=
    ⟨_, isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨b, eb⟩ : ∃ b : ℝ≥0, m.comap (Subtype.val : S → G) = b • (haar : Measure S) :=
    ⟨_, isMulLeftInvariant_eq_smul _ _⟩
  have hμ' : μ = a • (haar : Measure S).map Subtype.val := by
    calc μ = (μ.comap (Subtype.val : S → G)).map Subtype.val := hμM.symm
      _ = (a • (haar : Measure S)).map Subtype.val := by rw [ea]
      _ = _ := by rw [Measure.map_smul]
  have hm' : m = b • (haar : Measure S).map Subtype.val := by
    calc m = (m.comap (Subtype.val : S → G)).map Subtype.val := hmM.symm
      _ = (b • (haar : Measure S)).map Subtype.val := by rw [eb]
      _ = _ := by rw [Measure.map_smul]
  have ha0 : a ≠ 0 := by rintro rfl; apply hμ0; rw [hμ', zero_smul]
  refine ⟨((b / a : ℝ≥0) : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩
  rw [hm', hμ']
  ext s hs
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  rw [← mul_assoc, ← ENNReal.coe_mul, div_mul_cancel₀ b ha0]

/- English proof (translation)
Establish `hfμ : IsFiniteMeasureOnCompacts μ` using `⟨fun K hK => (haarOn_props N hN μ hμ).1 K hK⟩`. Establish `hfν : IsFiniteMeasureOnCompacts ν` using `⟨fun K hK => (haarOn_props N hN ν hν).1 K hK⟩`. Take `⟨c, hct, hc⟩` from `haar_unique N hN μ ν hμ.2.1 hμ.2.2.1 hμ.2.2.2 hfμ hν.2.2.1 hν.2.2.2 hfν`. Use `⟨c, ?_, hct, hc⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Apply `hν.2.1` to reduce the goal to its premises. Rewrite using `[hc, zero_smul]`.
-/
theorem haarOn_unique (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ ν : Measure G} (hμ : HaarOn N μ)
    (hν : HaarOn N ν) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ν = c • μ := by
  have hfμ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => (haarOn_props N hN μ hμ).1 K hK⟩
  have hfν : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => (haarOn_props N hN ν hν).1 K hK⟩
  obtain ⟨c, hct, hc⟩ :=
    haar_unique N hN μ ν hμ.2.1 hμ.2.2.1 hμ.2.2.2 hfμ hν.2.2.1 hν.2.2.2 hfν
  refine ⟨c, ?_, hct, hc⟩
  rintro rfl
  apply hν.2.1
  rw [hc, zero_smul]

/- English proof (translation)
Take `⟨hfin, hpos⟩` from `haarOn_props N hN μ hμ`. Take `⟨K, hK, hK1⟩` from `exists_compact_mem_nhds (1 : G)`. Use `⟨K, hK, ?_, hfin K hK⟩` and prove the remaining obligations. Establish `h1 : (1 : G) ∈ interior K` using `mem_interior_iff_mem_nhds.mpr hK1`. Conclude with `lt_of_lt_of_le (hpos _ isOpen_interior ⟨1, h1, N.one_mem⟩) (measure_mono interior_subset)`.
-/
theorem exists_K (N : Subgroup G) (hN : IsClosed (N : Set G)) (μ : Measure G) (hμ : HaarOn N μ) :
    ∃ K : Set G, IsCompact K ∧ 0 < μ K ∧ μ K < ⊤ := by
  obtain ⟨hfin, hpos⟩ := haarOn_props N hN μ hμ
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨K, hK, ?_, hfin K hK⟩
  have h1 : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.mpr hK1
  exact lt_of_lt_of_le (hpos _ isOpen_interior ⟨1, h1, N.one_mem⟩) (measure_mono interior_subset)

/- English proof (translation)
Establish `h'` using `congrArg (fun ν : Measure G => ν K) h`. Simplify using `only [Measure.smul_apply, smul_eq_mul] at h'`. Establish `h''` using `congrArg (· / μ K) h'`. Simplify `h''` using `[ENNReal.mul_div_cancel_right hK0.ne' hKt.ne]`.
-/
theorem smul_cancel {μ : Measure G} {K : Set G} (hK0 : 0 < μ K) (hKt : μ K < ⊤) {c d : ℝ≥0∞}
    (h : c • μ = d • μ) : c = d := by
  have h' := congrArg (fun ν : Measure G => ν K) h
  simp only [Measure.smul_apply, smul_eq_mul] at h'
  have h'' := congrArg (· / μ K) h'
  simpa [ENNReal.mul_div_cancel_right hK0.ne' hKt.ne] using h''

/- English proof (translation)
Take `⟨hσ, h0, hc, hi⟩` from `hμ`. Establish `hφm : Measurable φ` using `by rw [← he]; exact e.measurable`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hσ`. Establish `h1` using `e.toMeasurableEquiv.sigmaFinite_map (μ := μ)`.

Rewrite `h1` using `[Homeomorph.toMeasurableEquiv_coe, he]`. Conclude with `h1`. Conclude with `fun h => h0 ((Measure.map_eq_zero_iff hφm.aemeasurable).mp h)`. Rewrite using `[Measure.map_apply hφm hN.isOpen_compl.measurableSet]`. Conclude with `measure_mono_null (fun x hx hxN => hx (hNφ x hxN)) hc`.

Introduce `s hs`. Take `⟨s', hs', hss⟩` from `hl s hs`. Rewrite using `[Measure.map_map (measurable_const_mul s) hφm]`. Establish `h2 : (fun x => s * x) ∘ φ = φ ∘ (fun x => s' * x)` using `by funext x; exact hss x`. Rewrite using `[h2, ← Measure.map_map hφm (measurable_const_mul s'), hi s' hs']`.
-/
theorem haarOn_map (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    (φ : G → G) (e : G ≃ₜ G) (he : ⇑e = φ) (hNφ : ∀ x ∈ N, φ x ∈ N)
    (hl : ∀ s ∈ N, ∃ s' ∈ N, ∀ x, s * φ x = φ (s' * x)) : HaarOn N (μ.map φ) := by
  obtain ⟨hσ, h0, hc, hi⟩ := hμ
  have hφm : Measurable φ := by rw [← he]; exact e.measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI := hσ
    have h1 := e.toMeasurableEquiv.sigmaFinite_map (μ := μ)
    rw [Homeomorph.toMeasurableEquiv_coe, he] at h1
    exact h1
  · exact fun h => h0 ((Measure.map_eq_zero_iff hφm.aemeasurable).mp h)
  · rw [Measure.map_apply hφm hN.isOpen_compl.measurableSet]
    exact measure_mono_null (fun x hx hxN => hx (hNφ x hxN)) hc
  · intro s hs
    obtain ⟨s', hs', hss⟩ := hl s hs
    rw [Measure.map_map (measurable_const_mul s) hφm]
    have h2 : (fun x => s * x) ∘ φ = φ ∘ (fun x => s' * x) := by funext x; exact hss x
    rw [h2, ← Measure.map_map hφm (measurable_const_mul s'), hi s' hs']

/- English proof (translation)
The claim follows from `haarOn_map N hN hμ (fun x => x * n) (Homeomorph.mulRight n) (by ext x; simp) (fun x hx => N.mul_mem hx hn) (fun s hs => ⟨s, hs, fun x => (mul_assoc s x n).symm⟩)`.
-/
theorem haarOn_mulRight (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    {n : G} (hn : n ∈ N) : HaarOn N (μ.map (fun x => x * n)) := haarOn_map N hN hμ (fun x => x * n) (Homeomorph.mulRight n) (by ext x; simp)
    (fun x hx => N.mul_mem hx hn) (fun s hs => ⟨s, hs, fun x => (mul_assoc s x n).symm⟩)

/- English proof (translation)
The claim follows from `haarOn_map N hN hμ (fun x => a * x * a⁻¹) ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)) (by ext x; simp) (fun x hx => h1 x hx) (fun s hs => ⟨a⁻¹ * s * a, h2 s hs, fun x => by group⟩)`.
-/
theorem haarOn_conj (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    (a : G) (h1 : ∀ x ∈ N, a * x * a⁻¹ ∈ N) (h2 : ∀ x ∈ N, a⁻¹ * x * a ∈ N) :
    HaarOn N (μ.map (fun x => a * x * a⁻¹)) := haarOn_map N hN hμ (fun x => a * x * a⁻¹) ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹))
    (by ext x; simp) (fun x hx => h1 x hx) (fun s hs => ⟨a⁻¹ * s * a, h2 s hs, fun x => by group⟩)

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Use `push_neg at hx`. Establish `hxt : x ≠ ⊤`. Introduce and unpack `rfl`. Establish `h1` using `h 1`.

Simplify using `at h1`. Conclude with `hB h1`. Take `⟨p, hp⟩` from `pow_unbounded_of_one_lt B.toReal (by`. Establish `h2` using `(ENNReal.toReal_lt_toReal ENNReal.one_ne_top hxt).mpr hx`. Simplify using `using h2)`.

Establish `h3 : (x ^ p).toReal ≤ B.toReal` using `ENNReal.toReal_mono hB (h p)`. Rewrite `h3` using `[ENNReal.toReal_pow]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_one_of_pow_le {x B : ℝ≥0∞} (hB : B ≠ ⊤) (h : ∀ p : ℕ, x ^ p ≤ B) : x ≤ 1 := by
  by_contra hx
  push_neg at hx
  have hxt : x ≠ ⊤ := by
    rintro rfl
    have h1 := h 1
    simp at h1
    exact hB h1
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt B.toReal (by
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hxt).mpr hx
    simpa using h2)
  have h3 : (x ^ p).toReal ≤ B.toReal := ENNReal.toReal_mono hB (h p)
  rw [ENNReal.toReal_pow] at h3
  linarith

/- English proof (translation)
Take `⟨K, hK, hK0, hKt⟩` from `exists_K N hN μ hμ`. Establish `hfin` using `(haarOn_props N hN μ hμ).1`. Establish `hR : ∀ g ∈ N, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (fun x => x * g) = c • μ` using `fun g hg => haarOn_unique N hN hμ (haarOn_mulRight N hN hμ hg)`. Establish `hpow : ∀ n ∈ N, ∀ c : ℝ≥0∞, μ.map (fun x => x * n) = c • μ → ∀ p : ℕ, μ.map (fun x => x * n ^ p) = c ^ p • μ`. Introduce `n hn c hc p`.

Proceed by induction on `p with`. Consider the case `zero => simp [Measure.map_id']`. Consider the case `succ p ih`. Establish `h1 : (fun x : G => x * n ^ (p + 1)) = (fun x => x * n) ∘ (fun x => x * n ^ p)`. Use function extensionality and compare the values at `x`.

Simplify using `[pow_succ, mul_assoc]`. Rewrite using `[h1, ← Measure.map_map (measurable_mul_const n) (measurable_mul_const _), ih, Measure.map_smul, hc, smul_smul, pow_succ]`. Establish `hconj : ∀ a : G, (∀ x ∈ N, a * x * a⁻¹ ∈ N) → (∀ x ∈ N, a⁻¹ * x * a ∈ N) → ∀ m ∈ N, ∀ c : ℝ≥0∞, μ.map (fun x => x * m) = c • μ → μ.map (fun x => x * (a * m * a⁻¹)) = c • μ`. Introduce `a h1 h2 m hm c hc`. Take `⟨k, hk0, hkt, hk⟩` from `haarOn_unique N hN hμ (haarOn_conj N hN hμ a h1 h2)`.

Establish `hψm : Measurable (fun x : G => a * x * a⁻¹)` using `(measurable_const_mul a).mul_const a⁻¹`. Establish `hψim : Measurable (fun x : G => a⁻¹ * x * a)` using `(measurable_const_mul a⁻¹).mul_const a`. Establish `hid : (μ.map (fun x => a * x * a⁻¹)).map (fun x => a⁻¹ * x * a) = μ`. Rewrite using `[Measure.map_map hψim hψm]`. Establish `h3 : ((fun x : G => a⁻¹ * x * a) ∘ fun x => a * x * a⁻¹) = id`.

Use function extensionality and compare the values at `x`. Simplify using `[mul_assoc]`. Rewrite using `[h3, Measure.map_id]`. Rewrite `hid` using `[hk, Measure.map_smul]`. Establish `hback : μ.map (fun x => a⁻¹ * x * a) = k⁻¹ • μ`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.inv_mul_cancel hk0 hkt, one_smul]`. Use `_ = k⁻¹ • (k • μ.map (fun x => a⁻¹ * x * a)) := by rw [smul_smul]`. Use `_ = k⁻¹ • μ := by rw [hid]`. Establish `hcomp : (fun x : G => x * (a * m * a⁻¹)) = (fun x => a * x * a⁻¹) ∘ (fun x => x * m) ∘ (fun x => a⁻¹ * x * a)`.

Use function extensionality and compare the values at `x`. Simplify using `[mul_assoc]`. Rewrite using `[hcomp, ← Measure.map_map hψm ((measurable_mul_const m).comp hψim), ← Measure.map_map (measurable_mul_const m) hψim, hback, Measure.map_smul, hc, smul_smul, Measure.map_smul, hk, smul_smul]`. Use `congr 1`. Rewrite using `[mul_comm (k⁻¹ * c) k, ← mul_assoc, ENNReal.mul_inv_cancel hk0 hkt, one_mul]`.

Take `⟨S, hS⟩ : ∃ S : Set G, S = (fun q : G × G => q.1 * q.2⁻¹) '' (K ×ˢ C)` from `⟨_, rfl⟩`. Establish `hSc : IsCompact S`. Rewrite using `[hS]`. Conclude with `(hK.prod hC).image (continuous_fst.mul continuous_snd.inv)`. Establish `hBt : μ S ≠ ⊤` using `(hfin S hSc).ne`.

Establish `hbound : ∀ g ∈ C, ∀ e : ℝ≥0∞, μ.map (fun x => x * g) = e • μ → e * μ K ≤ μ S`. Introduce `g hg e he`. Establish `h1 : μ.map (fun x => x * g) K = e * μ K` using `by rw [he, Measure.smul_apply, smul_eq_mul]`. Rewrite `h1` using `[Measure.map_apply (measurable_mul_const g) hK.isClosed.measurableSet]`. Rewrite using `[← h1]`.

Apply `measure_mono` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[hS]`. Conclude with `⟨(x * g, g), ⟨hx, hg⟩, by simp⟩`. Establish `hle : ∀ n ∈ N, ∀ c : ℝ≥0∞, μ.map (fun x => x * n) = c • μ → c ≤ 1`.

Introduce `n hn c hc`. Apply `le_one_of_pow_le (B := μ S / μ K) (ENNReal.div_ne_top hBt hK0.ne')` to reduce the goal to its premises. Introduce `p`. Take `⟨a, ha1, ha2, haC⟩` from `hcon (n ^ p) (N.pow_mem hn p)`. Establish `h1` using `hconj a ha1 ha2 (n ^ p) (N.pow_mem hn p) (c ^ p) (hpow n hn c hc p)`.

Establish `h2` using `hbound _ haC (c ^ p) h1`. Conclude with `(ENNReal.le_div_iff_mul_le (Or.inl hK0.ne') (Or.inl hKt.ne)).mpr h2`. Introduce `n hn`. Take `⟨c, hc0, hct, hc⟩` from `hR n hn`. Take `⟨d, hd0, hdt, hd⟩` from `hR n⁻¹ (N.inv_mem hn)`.

Establish `hc1` using `hle n hn c hc`. Establish `hd1` using `hle n⁻¹ (N.inv_mem hn) d hd`. Establish `hcd : c * d = 1`. Establish `h1 : (μ.map (fun x => x * n)).map (fun x => x * n⁻¹) = μ`. Rewrite using `[Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]`.

Establish `h2 : ((fun x : G => x * n⁻¹) ∘ fun x => x * n) = id` using `by funext x; simp`. Rewrite using `[h2, Measure.map_id]`. Rewrite `h1` using `[hc, Measure.map_smul, hd, smul_smul]`. Conclude with `smul_cancel hK0 hKt (h1.trans (one_smul ℝ≥0∞ μ).symm)`. Establish `hc_eq : c = 1`.

Assume the negation of the conclusion as `hne`. Establish `hlt : c < 1` using `lt_of_le_of_ne hc1 hne`. Establish `h3 : c * d < 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h3` using `[hcd]`.

Conclude with `lt_irrefl _ h3`. Rewrite using `[hc, hc_eq, one_smul]`.
-/
theorem rightInv_of_contract (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    (C : Set G) (hC : IsCompact C)
    (hcon : ∀ n ∈ N, ∃ a : G, (∀ x ∈ N, a * x * a⁻¹ ∈ N) ∧ (∀ x ∈ N, a⁻¹ * x * a ∈ N) ∧ a * n * a⁻¹ ∈ C) :
    ∀ n ∈ N, μ.map (fun x => x * n) = μ := by
  obtain ⟨K, hK, hK0, hKt⟩ := exists_K N hN μ hμ
  have hfin := (haarOn_props N hN μ hμ).1
  have hR : ∀ g ∈ N, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (fun x => x * g) = c • μ :=
    fun g hg => haarOn_unique N hN hμ (haarOn_mulRight N hN hμ hg)
  have hpow : ∀ n ∈ N, ∀ c : ℝ≥0∞, μ.map (fun x => x * n) = c • μ →
      ∀ p : ℕ, μ.map (fun x => x * n ^ p) = c ^ p • μ := by
    intro n hn c hc p
    induction p with
    | zero => simp [Measure.map_id']
    | succ p ih =>
      have h1 : (fun x : G => x * n ^ (p + 1)) = (fun x => x * n) ∘ (fun x => x * n ^ p) := by
        funext x; simp [pow_succ, mul_assoc]
      rw [h1, ← Measure.map_map (measurable_mul_const n) (measurable_mul_const _), ih,
        Measure.map_smul, hc, smul_smul, pow_succ]
  have hconj : ∀ a : G, (∀ x ∈ N, a * x * a⁻¹ ∈ N) → (∀ x ∈ N, a⁻¹ * x * a ∈ N) →
      ∀ m ∈ N, ∀ c : ℝ≥0∞, μ.map (fun x => x * m) = c • μ →
        μ.map (fun x => x * (a * m * a⁻¹)) = c • μ := by
    intro a h1 h2 m hm c hc
    obtain ⟨k, hk0, hkt, hk⟩ := haarOn_unique N hN hμ (haarOn_conj N hN hμ a h1 h2)
    have hψm : Measurable (fun x : G => a * x * a⁻¹) := (measurable_const_mul a).mul_const a⁻¹
    have hψim : Measurable (fun x : G => a⁻¹ * x * a) := (measurable_const_mul a⁻¹).mul_const a
    have hid : (μ.map (fun x => a * x * a⁻¹)).map (fun x => a⁻¹ * x * a) = μ := by
      rw [Measure.map_map hψim hψm]
      have h3 : ((fun x : G => a⁻¹ * x * a) ∘ fun x => a * x * a⁻¹) = id := by
        funext x; simp [mul_assoc]
      rw [h3, Measure.map_id]
    rw [hk, Measure.map_smul] at hid
    have hback : μ.map (fun x => a⁻¹ * x * a) = k⁻¹ • μ := by
      calc μ.map (fun x => a⁻¹ * x * a) = (k⁻¹ * k) • μ.map (fun x => a⁻¹ * x * a) := by
            rw [ENNReal.inv_mul_cancel hk0 hkt, one_smul]
        _ = k⁻¹ • (k • μ.map (fun x => a⁻¹ * x * a)) := by rw [smul_smul]
        _ = k⁻¹ • μ := by rw [hid]
    have hcomp : (fun x : G => x * (a * m * a⁻¹)) =
        (fun x => a * x * a⁻¹) ∘ (fun x => x * m) ∘ (fun x => a⁻¹ * x * a) := by
      funext x; simp [mul_assoc]
    rw [hcomp, ← Measure.map_map hψm ((measurable_mul_const m).comp hψim),
      ← Measure.map_map (measurable_mul_const m) hψim, hback, Measure.map_smul, hc, smul_smul,
      Measure.map_smul, hk, smul_smul]
    congr 1
    rw [mul_comm (k⁻¹ * c) k, ← mul_assoc, ENNReal.mul_inv_cancel hk0 hkt, one_mul]
  obtain ⟨S, hS⟩ : ∃ S : Set G, S = (fun q : G × G => q.1 * q.2⁻¹) '' (K ×ˢ C) := ⟨_, rfl⟩
  have hSc : IsCompact S := by
    rw [hS]; exact (hK.prod hC).image (continuous_fst.mul continuous_snd.inv)
  have hBt : μ S ≠ ⊤ := (hfin S hSc).ne
  have hbound : ∀ g ∈ C, ∀ e : ℝ≥0∞, μ.map (fun x => x * g) = e • μ → e * μ K ≤ μ S := by
    intro g hg e he
    have h1 : μ.map (fun x => x * g) K = e * μ K := by rw [he, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply (measurable_mul_const g) hK.isClosed.measurableSet] at h1
    rw [← h1]
    apply measure_mono
    intro x hx
    rw [hS]
    exact ⟨(x * g, g), ⟨hx, hg⟩, by simp⟩
  have hle : ∀ n ∈ N, ∀ c : ℝ≥0∞, μ.map (fun x => x * n) = c • μ → c ≤ 1 := by
    intro n hn c hc
    apply le_one_of_pow_le (B := μ S / μ K) (ENNReal.div_ne_top hBt hK0.ne')
    intro p
    obtain ⟨a, ha1, ha2, haC⟩ := hcon (n ^ p) (N.pow_mem hn p)
    have h1 := hconj a ha1 ha2 (n ^ p) (N.pow_mem hn p) (c ^ p) (hpow n hn c hc p)
    have h2 := hbound _ haC (c ^ p) h1
    exact (ENNReal.le_div_iff_mul_le (Or.inl hK0.ne') (Or.inl hKt.ne)).mpr h2
  intro n hn
  obtain ⟨c, hc0, hct, hc⟩ := hR n hn
  obtain ⟨d, hd0, hdt, hd⟩ := hR n⁻¹ (N.inv_mem hn)
  have hc1 := hle n hn c hc
  have hd1 := hle n⁻¹ (N.inv_mem hn) d hd
  have hcd : c * d = 1 := by
    have h1 : (μ.map (fun x => x * n)).map (fun x => x * n⁻¹) = μ := by
      rw [Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
      have h2 : ((fun x : G => x * n⁻¹) ∘ fun x => x * n) = id := by funext x; simp
      rw [h2, Measure.map_id]
    rw [hc, Measure.map_smul, hd, smul_smul] at h1
    exact smul_cancel hK0 hKt (h1.trans (one_smul ℝ≥0∞ μ).symm)
  have hc_eq : c = 1 := by
    by_contra hne
    have hlt : c < 1 := lt_of_le_of_ne hc1 hne
    have h3 : c * d < 1 :=
      calc c * d ≤ c * 1 := by gcongr
        _ = c := mul_one c
        _ < 1 := hlt
    rw [hcd] at h3
    exact lt_irrefl _ h3
  rw [hc, hc_eq, one_smul]

/- English proof (translation)
Establish `hinv : HaarOn N (μ.map (fun x => x⁻¹))`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hμ.1`. Establish `h1` using `(Homeomorph.inv G).toMeasurableEquiv.sigmaFinite_map (μ := μ)`. Simplify using `using h1`.

Introduce `h`. Conclude with `hμ.2.1 ((Measure.map_eq_zero_iff measurable_inv.aemeasurable).mp h)`. Rewrite using `[Measure.map_apply measurable_inv hN.isOpen_compl.measurableSet]`. Conclude with `measure_mono_null (show (fun x : G => x⁻¹) ⁻¹' (N : Set G)ᶜ ⊆ (N : Set G)ᶜ from fun x hx hxN => hx (N.inv_mem hxN)) hμ.2.2.1`. Introduce `s hs`.

Rewrite using `[Measure.map_map (measurable_const_mul s) measurable_inv]`. Establish `h2 : (fun x => s * x) ∘ (fun x : G => x⁻¹) = (fun x : G => x⁻¹) ∘ (fun x => x * s⁻¹)`. Use function extensionality and compare the values at `x`. Simplify using `[mul_inv_rev]`. Rewrite using `[h2, ← Measure.map_map measurable_inv (measurable_mul_const s⁻¹), hR s⁻¹ (N.inv_mem hs)]`.

Take `⟨c, hc0, hct, hcμ⟩` from `haarOn_unique N hN hμ hinv`. Establish `hii : (μ.map (fun x : G => x⁻¹)).map (fun x : G => x⁻¹) = μ`. Rewrite using `[Measure.map_map measurable_inv measurable_inv]`. Establish `h3 : ((fun x : G => x⁻¹) ∘ fun x : G => x⁻¹) = id` using `by funext x; simp`. Rewrite using `[h3, Measure.map_id]`.

Establish `hcc : (c * c) • μ = (1 : ℝ≥0∞) • μ`. Rewrite using `[one_smul, mul_smul]`. Use `conv_rhs => rw [← hii, hcμ, Measure.map_smul, hcμ]`. Take `⟨K, hK, hK0, hKt⟩` from `exists_K N hN μ hμ`. Establish `h1 : c * c = 1` using `smul_cancel hK0 hKt hcc`.

Establish `h2 : c = 1`. Break down `lt_trichotomy c 1 with h | h | h` into its components or cases. It suffices to derive a contradiction. Establish `h4 : c * c < 1 * 1` using `ENNReal.mul_lt_mul h h`. Simplify using `[h1] at h4`.

Conclude with `h`. It suffices to derive a contradiction. Establish `h4 : 1 * 1 < c * c` using `ENNReal.mul_lt_mul h h`. Simplify using `[h1] at h4`. Rewrite using `[hcμ, h2, one_smul]`.
-/
theorem invInv_of_right (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    (hR : ∀ n ∈ N, μ.map (fun x => x * n) = μ) : μ.map (fun x => x⁻¹) = μ := by
  have hinv : HaarOn N (μ.map (fun x => x⁻¹)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · haveI := hμ.1
      have h1 := (Homeomorph.inv G).toMeasurableEquiv.sigmaFinite_map (μ := μ)
      simpa using h1
    · intro h; exact hμ.2.1 ((Measure.map_eq_zero_iff measurable_inv.aemeasurable).mp h)
    · rw [Measure.map_apply measurable_inv hN.isOpen_compl.measurableSet]
      exact measure_mono_null (show (fun x : G => x⁻¹) ⁻¹' (N : Set G)ᶜ ⊆ (N : Set G)ᶜ from
        fun x hx hxN => hx (N.inv_mem hxN)) hμ.2.2.1
    · intro s hs
      rw [Measure.map_map (measurable_const_mul s) measurable_inv]
      have h2 : (fun x => s * x) ∘ (fun x : G => x⁻¹) = (fun x : G => x⁻¹) ∘ (fun x => x * s⁻¹) := by
        funext x; simp [mul_inv_rev]
      rw [h2, ← Measure.map_map measurable_inv (measurable_mul_const s⁻¹), hR s⁻¹ (N.inv_mem hs)]
  obtain ⟨c, hc0, hct, hcμ⟩ := haarOn_unique N hN hμ hinv
  have hii : (μ.map (fun x : G => x⁻¹)).map (fun x : G => x⁻¹) = μ := by
    rw [Measure.map_map measurable_inv measurable_inv]
    have h3 : ((fun x : G => x⁻¹) ∘ fun x : G => x⁻¹) = id := by funext x; simp
    rw [h3, Measure.map_id]
  have hcc : (c * c) • μ = (1 : ℝ≥0∞) • μ := by
    rw [one_smul, mul_smul]
    conv_rhs => rw [← hii, hcμ, Measure.map_smul, hcμ]
  obtain ⟨K, hK, hK0, hKt⟩ := exists_K N hN μ hμ
  have h1 : c * c = 1 := smul_cancel hK0 hKt hcc
  have h2 : c = 1 := by
    rcases lt_trichotomy c 1 with h | h | h
    · exfalso
      have h4 : c * c < 1 * 1 := ENNReal.mul_lt_mul h h
      simp [h1] at h4
    · exact h
    · exfalso
      have h4 : 1 * 1 < c * c := ENNReal.mul_lt_mul h h
      simp [h1] at h4
  rw [hcμ, h2, one_smul]

end Abs

end PI.NMeasInv.UnitaryGroupMassFormula
