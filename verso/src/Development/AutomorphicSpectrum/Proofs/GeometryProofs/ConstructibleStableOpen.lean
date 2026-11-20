import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isClosed_of_stable_of_noetherian {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] (V : Set X)
    (hg : StableUnderGeneralization V) (hs : StableUnderSpecialization V) : IsClosed V := by
  have key : ∀ x ∈ V, irreducibleComponent x ⊆ V := by
    intro x hx y hy
    have hS : IsGenericPoint (isIrreducible_irreducibleComponent (x := x)).genericPoint
        (irreducibleComponent x) :=
      (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
        isClosed_irreducibleComponent
    exact hs (hS.specializes hy) (hg (hS.specializes mem_irreducibleComponent) hx)
  have hV : V = ⋃₀ {C | C ∈ irreducibleComponents X ∧ C ⊆ V} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x, key x hx⟩, mem_irreducibleComponent⟩
    · exact Set.sUnion_subset fun C hC => hC.2
  rw [hV, Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun C hC => hC.1)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_of_stable (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k))
    (hg : StableUnderGeneralization U) (hs : StableUnderSpecialization U) : IsOpen U := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stable_of_noetherian Uᶜ
    (stableUnderGeneralization_compl_iff.mpr hs) (stableUnderSpecialization_compl_iff.mpr hg)

end GlobalTheory.CompanionTheory.Ar.Approx
