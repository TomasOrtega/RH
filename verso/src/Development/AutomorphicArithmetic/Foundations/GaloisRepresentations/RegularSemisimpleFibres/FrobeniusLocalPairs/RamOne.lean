import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge

open ValuativeRel PositivityTheory.Rg.Tf.Loc

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem ramOne (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] (h : IsUnramifiedLoc k K) :
    GroundTheory.LocalField.ramificationIndex k K = 1 := by
  obtain ⟨π, hπ, hmin⟩ := h
  have hv := Valuation.integer.integers (valuation K)
  rw [← GroundTheory.LocalField.isUnramified_iff, ← GroundTheory.LocalField.map_maximalIdeal_eq_iff]
  have hπk : π ∈ 𝒪[k] := (GroundTheory.LocalField.algebraMap_mem_integer_iff k K π).1 (le_of_lt hπ)
  let p : 𝒪[k] := ⟨π, hπk⟩
  have hpK : ((algebraMap 𝒪[k] 𝒪[K] p : 𝒪[K]) : K) = algebraMap k K π := rfl
  have hp : p ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hv.one_of_isUnit (hu.map (algebraMap 𝒪[k] 𝒪[K]))
    change valuation K ((algebraMap 𝒪[k] 𝒪[K] p : 𝒪[K]) : K) = 1 at h1
    rw [hpK] at h1
    exact (ne_of_lt hπ) h1
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.2 (fun x hx => by
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact ((IsLocalRing.mem_maximalIdeal x).1 hx) (isUnit_of_map_unit _ _ hu))
  · intro x hx
    have hxlt : valuation K (x : K) < 1 := by
      by_contra hge
      have heq : valuation K (x : K) = 1 := le_antisymm x.2 (not_lt.1 hge)
      exact ((IsLocalRing.mem_maximalIdeal x).1 hx) (hv.isUnit_of_one' heq)
    have hle := hmin (x : K) hxlt
    rw [← hpK] at hle
    obtain ⟨z, hz⟩ := hv.dvd_of_le (x := x) (y := algebraMap 𝒪[k] 𝒪[K] p) hle
    rw [hz]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Equip the data with the indicated structure. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.resEx :
    UpperTheory.Gal.InertialTypesAlt.L.ResEx := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ hu
  have h1 := ramOne k K hu
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  refine ⟨𝓀[k], 𝓀[K], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsLocalRing.residue _, IsLocalRing.residue _, GroundTheory.LocalField.frobenius k K h1,
    GroundTheory.LocalField.residueAlgEquiv k K (GroundTheory.LocalField.frobenius k K h1), ?_⟩
  refine ⟨?_, IsLocalRing.residue_surjective, IsLocalRing.residue_surjective, ?_, ?_, ?_⟩
  · rw [← GroundTheory.LocalField.residueDegree_eq_finrank,
      GroundTheory.LocalField.residueDegree_eq_finrank_of_unramified k K h1]
  · intro x y h
    have e : y = algebraMap 𝒪[k] 𝒪[K] x := Subtype.ext h
    rw [e]
    rfl
  · intro x y h
    have e : y = GroundTheory.LocalField.integerAlgEquiv k K (GroundTheory.LocalField.frobenius k K h1) x :=
      Subtype.ext h
    rw [e, GroundTheory.LocalField.residueAlgEquiv_residue]
  · intro z
    rw [GroundTheory.LocalField.residueAlgEquiv_frobenius_apply, Fintype.card_eq_nat_card]
