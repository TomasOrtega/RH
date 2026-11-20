import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryBC GlobalTheory.LFun Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.PRep

/- English proof (translation)
Introduce `E _ _ _ n w hw f hf`. Take `⟨K', hKo, hKle, hK⟩` from `hf`. Establish `hU : UL n w = ⊤` using `if_pos hw`. Establish `hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w))`. Rewrite using `[hU]`.

Conclude with `isClosed_univ`. Use `⟨K'.subgroupOf (UL n w), hKo.preimage continuous_subtype_val, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `Subgroup.mem_subgroupOf.mpr (hKle (Subgroup.mem_subgroupOf.mp hx))`. Conclude with `hK.1.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal`.

Introduce `k hk x`. Conclude with `hK.2 k.1 (Subgroup.mem_subgroupOf.mp hk) x.1`.
-/
theorem UpperTheory.V.Z.Mult.lcLev :
    UpperTheory.V.Z.Mult.LcLev := by
  intro E _ _ _ n w hw f hf
  obtain ⟨K', hKo, hKle, hK⟩ := hf
  have hU : UL n w = ⊤ := if_pos hw
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    rw [hU]
    exact isClosed_univ
  refine ⟨K'.subgroupOf (UL n w), hKo.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hKle (Subgroup.mem_subgroupOf.mp hx))
  · exact hK.1.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal
  · intro k hk x
    exact hK.2 k.1 (Subgroup.mem_subgroupOf.mp hk) x.1
