import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

open scoped Topology
namespace GlobalTheory

/- English proof (translation)
Introduce `E Ω _ _ _ _ _`. Use `set F := maximalRealSubfield E`. Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Introduce `s hs`. Rewrite `hs` using `[map_one, krullTopology_mem_nhds_one_iff]`.

Take `⟨M, hM, hMs⟩` from `hs`. Set `b` to `Module.finBasis F M`. Use `set t : Set Ω := Set.range (fun i => ((b i : M) : Ω)) with ht_def`. Establish `hMt : M ≤ IntermediateField.adjoin F t`. Introduce `m hm`.

Establish `h` using `congrArg (fun y : M => (y : Ω)) (b.sum_repr ⟨m, hm⟩)`. Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h`. Rewrite using `[← h]`. Conclude with `sum_mem fun i _ => IntermediateField.smul_mem _ (IntermediateField.subset_adjoin F t (Set.mem_range_self i))`. Establish `hint : ∀ x ∈ t, IsIntegral E x`.

Introduce and unpack `x ⟨i, rfl⟩`. Establish `: IsIntegral F (b i)` using `IsIntegral.of_finite F _`. Conclude with `(IsIntegral.map (IsScalarTower.toAlgHom F M Ω) this).tower_top`. Use `haveI : Finite t := Set.finite_range _`. Use `haveI : FiniteDimensional E (IntermediateField.adjoin E t) := IntermediateField.finiteDimensional_adjoin hint`.

Rewrite using `[Filter.mem_map, krullTopology_mem_nhds_one_iff]`. Use `⟨IntermediateField.adjoin E t, inferInstance, fun σ hσ => hMs ?_⟩` and prove the remaining obligations. Establish `hH : IntermediateField.adjoin F t ≤ IntermediateField.fixedField (Subgroup.map (AlgEquiv.restrictScalarsHom F (A` using `Ω) (S := E)) (IntermediateField.adjoin E t).fixingSubgroup) := by`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `x hx`.

Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`. Introduce and unpack `f ⟨τ, hτ, rfl⟩`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.subset_adjoin E _ hx)`. Conclude with `IntermediateField.fixingSubgroup_antitone hMt ((IntermediateField.le_iff_le _ _).1 hH ⟨σ, hσ, rfl⟩)`.
-/
theorem restrictScalarsHom_maximalRealSubfield_continuous :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω],
    Continuous (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) : G E Ω →* G (maximalRealSubfield E) Ω) := by
  intro E Ω _ _ _ _ _
  set F := maximalRealSubfield E
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  let b := Module.finBasis F M
  set t : Set Ω := Set.range (fun i => ((b i : M) : Ω)) with ht_def
  have hMt : M ≤ IntermediateField.adjoin F t := by
    intro m hm
    have h := congrArg (fun y : M => (y : Ω)) (b.sum_repr ⟨m, hm⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    rw [← h]
    exact sum_mem fun i _ => IntermediateField.smul_mem _
      (IntermediateField.subset_adjoin F t (Set.mem_range_self i))
  have hint : ∀ x ∈ t, IsIntegral E x := by
    rintro x ⟨i, rfl⟩
    have : IsIntegral F (b i) := IsIntegral.of_finite F _
    exact (IsIntegral.map (IsScalarTower.toAlgHom F M Ω) this).tower_top
  haveI : Finite t := Set.finite_range _
  haveI : FiniteDimensional E (IntermediateField.adjoin E t) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin E t, inferInstance, fun σ hσ => hMs ?_⟩
  have hH : IntermediateField.adjoin F t ≤ IntermediateField.fixedField
      (Subgroup.map (AlgEquiv.restrictScalarsHom F (A := Ω) (S := E))
        (IntermediateField.adjoin E t).fixingSubgroup) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro f ⟨τ, hτ, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      (IntermediateField.subset_adjoin E _ hx)
  exact IntermediateField.fixingSubgroup_antitone hMt
    ((IntermediateField.le_iff_le _ _).1 hH ⟨σ, hσ, rfl⟩)

end GlobalTheory
