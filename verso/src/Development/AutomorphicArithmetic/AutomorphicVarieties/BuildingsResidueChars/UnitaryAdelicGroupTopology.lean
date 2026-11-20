import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

/- English proof (translation)
Introduce `E _ _ _ n`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL (E := E) (a := n)`.

Use `⟨inferInstance, (GlobalTheory.DefU.LocAdm.isClosed_UA (E := E) (n := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace, (Topology.IsEmbedding.subtypeVal (p := fun g : GA E n => g ∈ UA E n)).secondCountableTopology, ?_⟩` and prove the remaining obligations. Establish `hm : ∀ x : ratU E n, ((x : UA E n) : GA E n) ∈ latticeGL E n` using `fun x => by`. Take `⟨δ, hδ⟩` from `x.2`. Establish `h` using `GlobalTheory.CuspRep.CuspidalL2GL.ratGL_mem_latticeGL (E := E) δ`. Rewrite `h` using `[hδ]`.

Conclude with `h`. Set `f : ratU E n → latticeGL E n` to `fun x => ⟨_, hm x⟩`. Establish `hf : Continuous f` using `(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _`. Establish `hi : Function.Injective f` using `fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : latticeGL E n => (z : GA E n)) h))`. Conclude with `DiscreteTopology.of_continuous_injective hf hi`.
-/
theorem UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), T2Space (UA E n) ∧ LocallyCompactSpace (UA E n) ∧ SecondCountableTopology (UA E n) ∧ DiscreteTopology (ratU E n) := by
  intro E _ _ _ n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL (E := E) (a := n)
  refine ⟨inferInstance, (GlobalTheory.DefU.LocAdm.isClosed_UA (E := E) (n := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace,
    (Topology.IsEmbedding.subtypeVal (p := fun g : GA E n => g ∈ UA E n)).secondCountableTopology, ?_⟩
  have hm : ∀ x : ratU E n, ((x : UA E n) : GA E n) ∈ latticeGL E n := fun x => by
    obtain ⟨δ, hδ⟩ := x.2
    have h := GlobalTheory.CuspRep.CuspidalL2GL.ratGL_mem_latticeGL (E := E) δ
    rw [hδ] at h
    exact h
  let f : ratU E n → latticeGL E n := fun x => ⟨_, hm x⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : latticeGL E n => (z : GA E n)) h))
  exact DiscreteTopology.of_continuous_injective hf hi
