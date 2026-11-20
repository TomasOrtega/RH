import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.Higher
import GroundTheory.ProfiniteCohomology.InflationRestriction.FiveTerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]
  (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem fiveTerm_exact :
    Function.Injective (cohomologyInfl A N 1).hom ∧
      LinearMap.range (cohomologyInfl A N 1).hom = LinearMap.ker (cohomologyResInv A N) ∧
      LinearMap.range (cohomologyResInv A N) = LinearMap.ker (transgression A N hN) ∧
      LinearMap.range (transgression A N hN) = LinearMap.ker (cohomologyInfl A N 2).hom := by
  refine ⟨cohomologyInfl_one_injective A N, ?_, ?_, ?_⟩
  · ext h
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [coe_cohomologyResInv_apply, ZeroMemClass.coe_zero]
      have := congrArg (fun φ => ModuleCat.Hom.hom φ y) (cohomologyInfl_comp_cohomologyRes A N 0)
      simpa using this
    · intro hh
      exact exists_cohomologyInfl_one_eq A N h (congrArg Subtype.val hh)
  · ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact transgression_cohomologyResInv A N hN g
    · intro hh
      exact exists_cohomologyResInv_eq A N hN h hh
  · ext t
    constructor
    · rintro ⟨h, rfl⟩
      exact cohomologyInfl_transgression A N hN h
    · intro ht
      exact exists_transgression_eq A N hN t ht

include hN in

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem infRes_exact {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (cohomology (Rep.res N.subtype A) i)) :
    Function.Injective (cohomologyInfl A N q).hom ∧
      LinearMap.range (cohomologyInfl A N q).hom = LinearMap.ker (cohomologyRes A N q).hom :=
  ⟨cohomologyInfl_injective hN hq hA, range_cohomologyInfl_eq_ker_cohomologyRes hN hq hA⟩

end GroundTheory.ProfCoh
