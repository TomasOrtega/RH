import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.GabSep

/- English proof (translation)
Introduce `E Ω _ _ _ _ g hg`. Assume the negation of the conclusion as `hne`. Use `haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) := Subgroup.isClosed_topologicalClosure _`. Establish `hT1 : T1Space (Gab E Ω)` using `inferInstance`. Establish `hopen : IsOpen ({g}ᶜ : Set (Gab E Ω))` using `isOpen_compl_singleton`.

Establish `hmem : ((QuotientGroup.mk : G E Ω → Gab E Ω) ⁻¹' {g}ᶜ) ∈ nhds (1 : G E Ω)`. Use `(hopen.preimage QuotientGroup.continuous_mk).mem_nhds ?_` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, QuotientGroup.mk_one]`. Conclude with `fun h => hne h.symm`. Take `⟨L, hL, hsub⟩` from `(krullTopology_mem_nhds_one_iff E Ω _).mp hmem`.

Set `V : Subgroup (Gab E Ω)` to `L.fixingSubgroup.map (QuotientGroup.mk' _)`. Establish `hV : IsOpen (V : Set (Gab E Ω))`. Establish `: (V : Set (Gab E Ω)) = (QuotientGroup.mk : G E Ω → Gab E Ω) '' (L.fixingSubgroup : Set (G E Ω))`. Simplify using `[V, Subgroup.coe_map]`. Rewrite using `[this]`.

Conclude with `QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen L)`. Take `⟨σ, hσ, e⟩` from `Subgroup.mem_map.mp (hg V hV)`. Conclude with `hsub hσ (by simpa using e)`.
-/
theorem eq_one_of_forall_isOpen_subgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (g : Gab E Ω), (∀ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) → g ∈ U) → g = 1 := by
  intro E Ω _ _ _ _ g hg
  by_contra hne
  haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  have hT1 : T1Space (Gab E Ω) := inferInstance
  have hopen : IsOpen ({g}ᶜ : Set (Gab E Ω)) := isOpen_compl_singleton
  have hmem : ((QuotientGroup.mk : G E Ω → Gab E Ω) ⁻¹' {g}ᶜ) ∈ nhds (1 : G E Ω) := by
    refine (hopen.preimage QuotientGroup.continuous_mk).mem_nhds ?_
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, QuotientGroup.mk_one]
    exact fun h => hne h.symm
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hmem
  let V : Subgroup (Gab E Ω) := L.fixingSubgroup.map (QuotientGroup.mk' _)
  have hV : IsOpen (V : Set (Gab E Ω)) := by
    have : (V : Set (Gab E Ω)) = (QuotientGroup.mk : G E Ω → Gab E Ω) '' (L.fixingSubgroup : Set (G E Ω)) := by
      simp [V, Subgroup.coe_map]
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen L)
  obtain ⟨σ, hσ, e⟩ := Subgroup.mem_map.mp (hg V hV)
  exact hsub hσ (by simpa using e)

end GlobalTheory.GabSep
