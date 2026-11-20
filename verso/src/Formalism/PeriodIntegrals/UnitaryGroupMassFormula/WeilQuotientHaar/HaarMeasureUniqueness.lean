import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal

namespace QPK

def toSub {G : Type} [Group G] (K : Set G) (hK : IsGrp K) : Subgroup G where
  carrier := K
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2 _ ha

section Sub

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `hv : Measurable (Subtype.val : K' → G)` using `measurable_subtype_coe`. Establish `hm : Measurable (fun x : K' => g * x)`. Establish `h : Measurable (fun x : K' => (g : G) * (x : G))` using `(measurable_const_mul (g : G)).comp hv`. Conclude with `h.subtype_mk`. Rewrite using `[Measure.map_map hv hm, Measure.map_map (measurable_const_mul _) hv]`.

Both sides reduce to the same expression.
-/
lemma map_val_mul (K' : Subgroup G) (g : K') (α : Measure K') :
    (α.map (fun x => g * x)).map Subtype.val = (α.map Subtype.val).map (fun x => (g : G) * x) := by
  have hv : Measurable (Subtype.val : K' → G) := measurable_subtype_coe
  have hm : Measurable (fun x : K' => g * x) := by
    have h : Measurable (fun x : K' => (g : G) * (x : G)) := (measurable_const_mul (g : G)).comp hv
    exact h.subtype_mk
  rw [Measure.map_map hv hm, Measure.map_map (measurable_const_mul _) hv]
  rfl

end Sub

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ K hKc hK`. Set `H : Subgroup G` to `toSub K hK`. Establish `hHc : IsClosed (H : Set G)` using `hKc`. Establish `hemb : Topology.IsClosedEmbedding (Subtype.val : H → G)` using `hHc.isClosedEmbedding_subtypeVal`. Use `haveI : LocallyCompactSpace H := hemb.locallyCompactSpace`.

Establish `hv : Measurable (Subtype.val : H → G)` using `measurable_subtype_coe`. Set `α : Measure H` to `Measure.haar`. Establish `hfin : IsFiniteMeasureOnCompacts (α.map Subtype.val)`. Use `⟨fun C hC => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hv hC.isClosed.measurableSet]`.

Conclude with `(hemb.isCompact_preimage hC).measure_lt_top`. Use `⟨α.map Subtype.val, ⟨?_, ?_, ?_, ?_⟩, hfin, ?_⟩` and prove the remaining obligations. Use `infer_instance`. Introduce `h`. Rewrite `h` using `[Measure.map_eq_zero_iff hv.aemeasurable]`.

Conclude with `(Measure.measure_univ_pos.mp (isOpen_univ.measure_pos α Set.univ_nonempty)) h`. Rewrite using `[Measure.map_apply hv hKc.measurableSet.compl]`. Establish `h : (Subtype.val : H → G) ⁻¹' Kᶜ = ∅` using `Set.eq_empty_iff_forall_notMem.2 fun x hx => hx x.2`. Rewrite using `[h, measure_empty]`. Introduce `s hs`.

Establish `h` using `map_val_mul H ⟨s, hs⟩ α`. Rewrite `h` using `[map_mul_left_eq_self]`. Conclude with `h.symm`. Introduce `U hU ⟨x, hxU, hxK⟩`. Rewrite using `[Measure.map_apply hv hU.measurableSet]`.

Conclude with `(hU.preimage continuous_subtype_val).measure_ne_zero α ⟨⟨x, hxK⟩, hxU⟩`.
-/
theorem haar_measure_existence : HaarExist := by
  intro G _ _ _ _ _ _ _ _ K hKc hK
  let H : Subgroup G := toSub K hK
  have hHc : IsClosed (H : Set G) := hKc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : H → G) := hHc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace H := hemb.locallyCompactSpace
  have hv : Measurable (Subtype.val : H → G) := measurable_subtype_coe
  let α : Measure H := Measure.haar
  have hfin : IsFiniteMeasureOnCompacts (α.map Subtype.val) := by
    refine ⟨fun C hC => ?_⟩
    rw [Measure.map_apply hv hC.isClosed.measurableSet]
    exact (hemb.isCompact_preimage hC).measure_lt_top
  refine ⟨α.map Subtype.val, ⟨?_, ?_, ?_, ?_⟩, hfin, ?_⟩
  · infer_instance
  · intro h
    rw [Measure.map_eq_zero_iff hv.aemeasurable] at h
    exact (Measure.measure_univ_pos.mp (isOpen_univ.measure_pos α Set.univ_nonempty)) h
  · rw [Measure.map_apply hv hKc.measurableSet.compl]
    have h : (Subtype.val : H → G) ⁻¹' Kᶜ = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx => hx x.2
    rw [h, measure_empty]
  · intro s hs
    have h := map_val_mul H ⟨s, hs⟩ α
    rw [map_mul_left_eq_self] at h
    exact h.symm
  · intro U hU ⟨x, hxU, hxK⟩
    rw [Measure.map_apply hv hU.measurableSet]
    exact (hU.preimage continuous_subtype_val).measure_ne_zero α ⟨⟨x, hxK⟩, hxU⟩

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ K hKc hK μ ν hμ hν`. Set `H : Subgroup G` to `toSub K hK`. Establish `hHc : IsClosed (H : Set G)` using `hKc`. Use `haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)`.

Establish `hme : MeasurableEmbedding (Subtype.val : H → G)` using `MeasurableEmbedding.subtype_coe hKc.measurableSet`. Set `K₀ : TopologicalSpace.PositiveCompacts H` to `Classical.arbitrary _`. Establish `key : ∀ ρ : Measure G, InvOn ρ K → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ρ = c • (Measure.haarMeasure K₀).map Subtype.val`. Introduce `ρ ⟨hσ, h0, hc, hinv⟩`. Set `ρ' : Measure H` to `ρ.comap Subtype.val`.

Establish `hback : ρ'.map Subtype.val = ρ`. Rewrite using `[hme.map_comap, Subtype.range_coe]`. Conclude with `Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc)`. Use `haveI : SigmaFinite ρ' := SigmaFinite.of_map ρ' hme.measurable.aemeasurable (by rw [hback]; exact hσ)`. Use `haveI : IsMulLeftInvariant ρ' := by`.

Use `⟨fun g => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Take `⟨c, hK0⟩ : ∃ c : ℝ≥0∞, ρ' = c • Measure.haarMeasure K₀` from `⟨_, Measure.haarMeasure_unique ρ' K₀⟩`. Establish `hρ : ρ = c • (Measure.haarMeasure K₀).map Subtype.val`. Rewrite using `[← hback, hK0, Measure.map_smul]`.

Use `⟨c, ?_, ?_, hρ⟩` and prove the remaining obligations. Introduce `hz`. Apply `h0` to reduce the goal to its premises. Rewrite using `[hρ, hz, zero_smul]`. Introduce `htop`.

Establish `hne : Measure.haarMeasure K₀ (⋃ n, spanningSets ρ' n) ≠ 0`. Rewrite using `[iUnion_spanningSets]`. Conclude with `(lt_of_lt_of_le zero_lt_one ((Measure.haarMeasure_self (K₀ := K₀)).symm.le.trans (measure_mono (Set.subset_univ _)))).ne'`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, Measure.haarMeasure K₀ (spanningSets ρ' n) ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Conclude with `hne (measure_iUnion_null_iff.2 hall)`. Establish `h2 : ρ' (spanningSets ρ' n) = (c • Measure.haarMeasure K₀) (spanningSets ρ' n)` using `congrArg (fun m : Measure H => m (spanningSets ρ' n)) hK0`. Establish `h3` using `measure_spanningSets_lt_top ρ' n`. Rewrite `h3` using `[h2, Measure.smul_apply, htop, smul_eq_mul, ENNReal.top_mul hn]`.

Conclude with `lt_irrefl _ h3`. Take `⟨a, ha0, hat, hμ'⟩` from `key μ hμ`. Take `⟨b, hb0, hbt, hν'⟩` from `key ν hν`. Use `⟨a / b, (ENNReal.div_pos ha0 hbt).ne', ENNReal.div_ne_top hat hb0, ?_⟩` and prove the remaining obligations. Rewrite using `[hμ', hν', smul_smul, ENNReal.div_mul_cancel hb0 hbt]`.
-/
theorem haar_measure_uniqueness : HaarUniq := by
  intro G _ _ _ _ _ _ _ _ K hKc hK μ ν hμ hν
  let H : Subgroup G := toSub K hK
  have hHc : IsClosed (H : Set G) := hKc
  haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hme : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hKc.measurableSet
  let K₀ : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have key : ∀ ρ : Measure G, InvOn ρ K → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ρ = c • (Measure.haarMeasure K₀).map Subtype.val := by
    intro ρ ⟨hσ, h0, hc, hinv⟩
    let ρ' : Measure H := ρ.comap Subtype.val
    have hback : ρ'.map Subtype.val = ρ := by
      rw [hme.map_comap, Subtype.range_coe]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc)
    haveI : SigmaFinite ρ' :=
      SigmaFinite.of_map ρ' hme.measurable.aemeasurable (by rw [hback]; exact hσ)
    haveI : IsMulLeftInvariant ρ' := by
      refine ⟨fun g => ?_⟩
      calc ρ'.map (g * ·) = ((ρ'.map (g * ·)).map Subtype.val).comap Subtype.val :=
            (hme.comap_map _).symm
        _ = ((ρ'.map Subtype.val).map ((g : G) * ·)).comap Subtype.val := by rw [map_val_mul]
        _ = ρ' := by rw [hback, hinv (g : G) g.2]
    obtain ⟨c, hK0⟩ : ∃ c : ℝ≥0∞, ρ' = c • Measure.haarMeasure K₀ :=
      ⟨_, Measure.haarMeasure_unique ρ' K₀⟩
    have hρ : ρ = c • (Measure.haarMeasure K₀).map Subtype.val := by
      rw [← hback, hK0, Measure.map_smul]
    refine ⟨c, ?_, ?_, hρ⟩
    · intro hz
      apply h0
      rw [hρ, hz, zero_smul]
    · intro htop
      have hne : Measure.haarMeasure K₀ (⋃ n, spanningSets ρ' n) ≠ 0 := by
        rw [iUnion_spanningSets]
        exact (lt_of_lt_of_le zero_lt_one
          ((Measure.haarMeasure_self (K₀ := K₀)).symm.le.trans (measure_mono (Set.subset_univ _)))).ne'
      obtain ⟨n, hn⟩ : ∃ n, Measure.haarMeasure K₀ (spanningSets ρ' n) ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hne (measure_iUnion_null_iff.2 hall)
      have h2 : ρ' (spanningSets ρ' n) = (c • Measure.haarMeasure K₀) (spanningSets ρ' n) :=
        congrArg (fun m : Measure H => m (spanningSets ρ' n)) hK0
      have h3 := measure_spanningSets_lt_top ρ' n
      rw [h2, Measure.smul_apply, htop, smul_eq_mul, ENNReal.top_mul hn] at h3
      exact lt_irrefl _ h3
  obtain ⟨a, ha0, hat, hμ'⟩ := key μ hμ
  obtain ⟨b, hb0, hbt, hν'⟩ := key ν hν
  refine ⟨a / b, (ENNReal.div_pos ha0 hbt).ne', ENNReal.div_ne_top hat hb0, ?_⟩
  rw [hμ', hν', smul_smul, ENNReal.div_mul_cancel hb0 hbt]

end QPK
