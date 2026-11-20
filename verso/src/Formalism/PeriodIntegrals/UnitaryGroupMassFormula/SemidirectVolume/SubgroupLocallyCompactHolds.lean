import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

noncomputable section

namespace PI.VolSemiDirect.W

/- English proof (translation)
Introduce `X _ _ Γ K hX hK hΓc hΓd`. Take `⟨hlc, hsc, ht2, htg⟩` from `hX`. Use `haveI := hlc`. Use `haveI := hsc`. Use `haveI := ht2`.

Use `haveI := htg`. Use `haveI := hΓc`. Use `haveI := hΓd`. Set `f : ratG Γ K → Γ` to `fun x => ⟨(x : K).1, (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 x.2)).1⟩`. Use `⟨⟨hK.isClosedEmbedding_subtypeVal.locallyCompactSpace, Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance, inferInstance⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `hf : Function.Injective f`. Introduce `a b h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h'` using `congrArg (fun y : Γ => (y : X)) h`.

Conclude with `h'`. Conclude with `hf.countable`. Establish `hcont : Continuous f`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Conclude with `continuous_subtype_val.comp continuous_subtype_val`.

Establish `hemb : Topology.IsEmbedding f`. Apply `Topology.IsEmbedding.of_comp hcont continuous_subtype_val` to reduce the goal to its premises. Use `show Topology.IsEmbedding (fun x : ratG Γ K => ((x : K) : X))`. Conclude with `Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal`. Conclude with `hemb.discreteTopology`.
-/
theorem subgroup_locally_compact_holds : SubLCSC := by
  intro X _ _ Γ K hX hK hΓc hΓd
  obtain ⟨hlc, hsc, ht2, htg⟩ := hX
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := htg
  haveI := hΓc
  haveI := hΓd
  let f : ratG Γ K → Γ := fun x => ⟨(x : K).1, (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 x.2)).1⟩
  refine ⟨⟨hK.isClosedEmbedding_subtypeVal.locallyCompactSpace, Topology.IsEmbedding.subtypeVal.secondCountableTopology,
    inferInstance, inferInstance⟩, ?_, ?_⟩
  · have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg (fun y : Γ => (y : X)) h
      exact h'
    exact hf.countable
  · have hcont : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hemb : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hcont continuous_subtype_val
      show Topology.IsEmbedding (fun x : ratG Γ K => ((x : K) : X))
      exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology

end PI.VolSemiDirect.W
