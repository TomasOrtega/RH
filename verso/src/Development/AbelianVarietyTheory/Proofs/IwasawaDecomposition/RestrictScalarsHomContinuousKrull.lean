import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory

/- English proof (translation)
Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`. Rewrite `hs` using `[krullTopology_mem_nhds_one_iff]`. Take `⟨L, hL, hLs⟩` from `hs`.

Set `b` to `Module.finBasis E L`. Establish `hint : ∀ i, IsIntegral K ((b i : L) : Ω)` using `fun i => ((IsIntegral.of_finite E (b i)).map (IsScalarTower.toAlgHom E L Ω)).tower_top`. Establish `hN : ⋂ i, ((IntermediateField.adjoin K {((b i : L) : Ω)}).fixingSubgroup : Set (G K Ω)) ∈ nhds (1 : G K Ω)` using `Filter.iInter_mem.mpr fun i => by haveI := IntermediateField.adjoin.finiteDimensional (hint i)`. Conclude with `(IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)`. Rewrite using `[Filter.mem_map]`.

Use `Filter.mem_of_superset hN ?_` and prove the remaining obligations. Introduce `σ hσ`. Apply `hLs` to reduce the goal to its premises. Simplify using `only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Establish `hb : ∀ i, σ ((b i : L) : Ω) = ((b i : L) : Ω)` using `fun i => hσ i _ (IntermediateField.mem_adjoin_simple_self K _)`. Take `⟨y, rfl⟩ : ∃ y : L, (y : Ω) = x` from `⟨⟨x, hx⟩, rfl⟩`. Rewrite using `[← b.sum_repr y]`. Express the relevant statement in the definitionally equal form `(AlgEquiv.restrictScalars E σ) _ = _`.

Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[AlgEquiv.restrictScalars_apply, hb]`.
-/
theorem restrictScalarsHom_continuous_krull (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (K : IntermediateField E Ω) :
    Continuous (AlgEquiv.restrictScalarsHom E : G K Ω →* G E Ω) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨L, hL, hLs⟩ := hs
  let b := Module.finBasis E L
  have hint : ∀ i, IsIntegral K ((b i : L) : Ω) := fun i =>
    ((IsIntegral.of_finite E (b i)).map (IsScalarTower.toAlgHom E L Ω)).tower_top
  have hN : ⋂ i, ((IntermediateField.adjoin K {((b i : L) : Ω)}).fixingSubgroup : Set (G K Ω))
      ∈ nhds (1 : G K Ω) := Filter.iInter_mem.mpr fun i => by
    haveI := IntermediateField.adjoin.finiteDimensional (hint i)
    exact (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hN ?_
  intro σ hσ
  apply hLs
  simp only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, σ ((b i : L) : Ω) = ((b i : L) : Ω) := fun i =>
    hσ i _ (IntermediateField.mem_adjoin_simple_self K _)
  obtain ⟨y, rfl⟩ : ∃ y : L, (y : Ω) = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← b.sum_repr y]
  change (AlgEquiv.restrictScalars E σ) _ = _
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgEquiv.restrictScalars_apply, hb]

end GlobalTheory
