import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

noncomputable section

open MeasureTheory Measure Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf

section Abs

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `he : MeasurableEmbedding ((↑) : H → G)` using `MeasurableEmbedding.subtype_coe hH.measurableSet`. Rewrite using `[he.map_comap]`. Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations. Rewrite using `[ae_iff]`. Use `le_antisymm (le_trans (measure_mono ?_) hc.le) zero_le` and prove the remaining obligations.

Introduce `x hx h`. Conclude with `hx ⟨⟨x, h⟩, rfl⟩`.
-/
theorem map_comap_subgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G)
    (hc : μ (H : Set G)ᶜ = 0) : (μ.comap ((↑) : H → G)).map ((↑) : H → G) = μ := by
  have he : MeasurableEmbedding ((↑) : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  rw [he.map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  refine le_antisymm (le_trans (measure_mono ?_) hc.le) zero_le
  intro x hx h
  exact hx ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
Establish `he : MeasurableEmbedding ((↑) : H → G)` using `MeasurableEmbedding.subtype_coe hH.measurableSet`. Establish `hmap : (μ.comap ((↑) : H → G)).map ((↑) : H → G) = μ` using `map_comap_subgroup H hH μ hc`. Establish `hce : Topology.IsClosedEmbedding ((↑) : H → G)` using `by first`. Consider the case `exact hH.isClosedEmbedding_subtypeVal`. Consider the case `exact hH.closedEmbedding_subtype_val`.

Use `haveI : LocallyCompactSpace H := hce.locallyCompactSpace`. Use `haveI : SigmaFinite (μ.comap ((↑) : H → G)) := by`. Use `SigmaFinite.of_map _ he.measurable.aemeasurable ?_` and prove the remaining obligations. Rewrite using `[hmap]`. Conclude with `hσ`.

Use `haveI : IsMulLeftInvariant (μ.comap ((↑) : H → G)) := by`. Prove the components needed by the constructor for the conclusion. Introduce `g`. Establish `hm1 : Measurable (fun x : H => g * x)` using `measurable_const_mul g`. Establish `hm2 : Measurable (fun x : G => (g : G) * x)` using `measurable_const_mul (g : G)`.

Establish `key : ((μ.comap ((↑) : H → G)).map (fun x : H => g * x)).map ((↑) : H → G) = μ`. Rewrite using `[Measure.map_map he.measurable hm1]`. Establish `hcomp : ((↑) : H → G) ∘ (fun x : H => g * x) = (fun x : G => (g : G) * x) ∘ ((↑) : H → G)` using `rfl`. Rewrite using `[hcomp, ← Measure.map_map hm2 he.measurable, hmap]`. Conclude with `hinv g g.2`.

Rewrite using `[← he.comap_map ((μ.comap ((↑) : H → G)).map (fun x : H => g * x)), key]`. Take `⟨K, hK, hK1⟩` from `exists_compact_mem_nhds (1 : H)`. Establish `hKpos : (Measure.haar : Measure H) K ≠ 0` using `by first`. Consider the case `exact (measure_pos_of_mem_nhds _ hK1).ne'`. Consider the case `exact (measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'`.

Establish `hKfin : (Measure.haar : Measure H) K < ⊤` using `hK.measure_lt_top`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hKpos` to reduce the goal to its premises.

Establish `hU : K = ⋃ n, K ∩ spanningSets (μ.comap ((↑) : H → G)) n`. Rewrite using `[← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]`. Rewrite using `[hU]`. Conclude with `measure_iUnion_null hcon`. Establish `hsm : MeasurableSet (K ∩ spanningSets (μ.comap ((↑) : H → G)) n)` using `hK.measurableSet.inter (measurableSet_spanningSets _ n)`.

Establish `hsfin : (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤` using `(lt_of_le_of_lt (measure_mono Set.inter_subset_left) hKfin).ne`. Establish `hνfin : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤` using `(lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_spanningSets_lt_top _ n)).ne`. Use `haveI : BorelSpace H := by first`. Consider the case `infer_instance`. Consider the case `exact Subtype.borelSpace _`.

Use `haveI : SecondCountableTopology H := by first`. Consider the case `infer_instance`. Consider the case `exact TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : MeasurableMul₂ H := by first`. Consider the case `infer_instance`.

Consider the case `exact ContinuousMul.measurableMul₂`. Use `haveI : MeasurableInv H := by first`. Consider the case `infer_instance`. Consider the case `exact ContinuousInv.measurableInv`. Establish `heq` using `measure_eq_div_smul (μ.comap ((↑) : H → G)) (Measure.haar : Measure H) hn hsfin`.

Establish `hc0 : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) / (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ 0`. Introduce `h`. Rewrite `heq` using `[h, zero_smul]`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← hmap, heq, Measure.map_zero]`.

Establish `hctop : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) / (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤` using `(ENNReal.div_lt_top hνfin hn).ne`. Establish `hHaar : (μ.comap ((↑) : H → G)).IsHaarMeasure`. Rewrite using `[heq]`. Use `first`. Consider the case `exact Measure.isHaarMeasure_smul _ hc0 hctop`.

Consider the case `exact IsHaarMeasure.smul _ hc0 hctop`. Consider the case `exact isHaarMeasure_smul _ hc0 hctop`. Use `haveI := hHaar`. Use `⟨hHaar, fun K' hK' => ?_, fun U hU hne => ?_⟩` and prove the remaining obligations. Rewrite using `[← hmap, he.map_apply]`.

Conclude with `(hce.isCompact_preimage hK').measure_lt_top`. Take `⟨x, hxU, hxH⟩` from `hne`. Rewrite using `[← hmap, he.map_apply]`. Conclude with `(hU.preimage continuous_subtype_val).measure_pos _ ⟨⟨x, hxH⟩, hxU⟩`.
-/
theorem haarOnSet_isHaar (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure G) (hσ : SigmaFinite μ)
    (h0 : μ ≠ 0) (hc : μ (H : Set G)ᶜ = 0) (hinv : ∀ s ∈ H, μ.map (fun x => s * x) = μ) :
    (μ.comap ((↑) : H → G)).IsHaarMeasure ∧ (∀ K : Set G, IsCompact K → μ K < ⊤) ∧
      ∀ U : Set G, IsOpen U → (U ∩ (H : Set G)).Nonempty → 0 < μ U := by
  have he : MeasurableEmbedding ((↑) : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  have hmap : (μ.comap ((↑) : H → G)).map ((↑) : H → G) = μ := map_comap_subgroup H hH μ hc
  have hce : Topology.IsClosedEmbedding ((↑) : H → G) := by
    first
      | exact hH.isClosedEmbedding_subtypeVal
      | exact hH.closedEmbedding_subtype_val
  haveI : LocallyCompactSpace H := hce.locallyCompactSpace
  haveI : SigmaFinite (μ.comap ((↑) : H → G)) := by
    refine SigmaFinite.of_map _ he.measurable.aemeasurable ?_
    rw [hmap]
    exact hσ
  haveI : IsMulLeftInvariant (μ.comap ((↑) : H → G)) := by
    constructor
    intro g
    have hm1 : Measurable (fun x : H => g * x) := measurable_const_mul g
    have hm2 : Measurable (fun x : G => (g : G) * x) := measurable_const_mul (g : G)
    have key : ((μ.comap ((↑) : H → G)).map (fun x : H => g * x)).map ((↑) : H → G) = μ := by
      rw [Measure.map_map he.measurable hm1]
      have hcomp : ((↑) : H → G) ∘ (fun x : H => g * x) = (fun x : G => (g : G) * x) ∘ ((↑) : H → G) := rfl
      rw [hcomp, ← Measure.map_map hm2 he.measurable, hmap]
      exact hinv g g.2
    rw [← he.comap_map ((μ.comap ((↑) : H → G)).map (fun x : H => g * x)), key]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have hKpos : (Measure.haar : Measure H) K ≠ 0 := by
    first
      | exact (measure_pos_of_mem_nhds _ hK1).ne'
      | exact (measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hKfin : (Measure.haar : Measure H) K < ⊤ := hK.measure_lt_top
  obtain ⟨n, hn⟩ : ∃ n, (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hKpos
    have hU : K = ⋃ n, K ∩ spanningSets (μ.comap ((↑) : H → G)) n := by
      rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
    rw [hU]
    exact measure_iUnion_null hcon
  have hsm : MeasurableSet (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) :=
    hK.measurableSet.inter (measurableSet_spanningSets _ n)
  have hsfin : (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hKfin).ne
  have hνfin : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_spanningSets_lt_top _ n)).ne
  haveI : BorelSpace H := by
    first
      | infer_instance
      | exact Subtype.borelSpace _
  haveI : SecondCountableTopology H := by
    first
      | infer_instance
      | exact TopologicalSpace.Subtype.secondCountableTopology _
  haveI : MeasurableMul₂ H := by
    first
      | infer_instance
      | exact ContinuousMul.measurableMul₂
  haveI : MeasurableInv H := by
    first
      | infer_instance
      | exact ContinuousInv.measurableInv
  have heq := measure_eq_div_smul (μ.comap ((↑) : H → G)) (Measure.haar : Measure H) hn hsfin
  have hc0 : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) /
      (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ 0 := by
    intro h
    rw [h, zero_smul] at heq
    apply h0
    rw [← hmap, heq, Measure.map_zero]
  have hctop : (μ.comap ((↑) : H → G)) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) /
      (Measure.haar : Measure H) (K ∩ spanningSets (μ.comap ((↑) : H → G)) n) ≠ ⊤ :=
    (ENNReal.div_lt_top hνfin hn).ne
  have hHaar : (μ.comap ((↑) : H → G)).IsHaarMeasure := by
    rw [heq]
    first
      | exact Measure.isHaarMeasure_smul _ hc0 hctop
      | exact IsHaarMeasure.smul _ hc0 hctop
      | exact isHaarMeasure_smul _ hc0 hctop
  haveI := hHaar
  refine ⟨hHaar, fun K' hK' => ?_, fun U hU hne => ?_⟩
  · rw [← hmap, he.map_apply]
    exact (hce.isCompact_preimage hK').measure_lt_top
  · obtain ⟨x, hxU, hxH⟩ := hne
    rw [← hmap, he.map_apply]
    exact (hU.preimage continuous_subtype_val).measure_pos _ ⟨⟨x, hxH⟩, hxU⟩

end Abs

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Conclude with `haarOnSet_isHaar H hH μ h.1 h.2.1 h.2.2.1 h.2.2.2`.
-/
theorem haarOnSet_isHaar_inst (H : Subgroup I.Ginf) (hH : IsClosed (H : Set I.Ginf)) (μ : Measure I.Ginf)
    (h : Formalism.L2.SG.HidaSetting.IsHaarOnSet I (H : Set I.Ginf) μ) :
    (μ.comap ((↑) : H → I.Ginf)).IsHaarMeasure ∧ (∀ K : Set I.Ginf, IsCompact K → μ K < ⊤) ∧
      ∀ U : Set I.Ginf, IsOpen U → (U ∩ (H : Set I.Ginf)).Nonempty → 0 < μ U := by
  exact haarOnSet_isHaar H hH μ h.1 h.2.1 h.2.2.1 h.2.2.2

end Inst

end Formalism.L2.SG.Pf
