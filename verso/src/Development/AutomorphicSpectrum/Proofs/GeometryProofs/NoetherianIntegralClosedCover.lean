import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

open TopologicalSpace in

/- English proof (translation)
Use `haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z`. Establish `hr : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (Z : Set X)`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Use `haveI : IrreducibleSpace (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) := Subtype.irreducibleSpace (by rw [hr]; exact h)`. Set `f` to `(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph`.

Use `haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := Function.Surjective.irreducibleSpace f.symm.continuous f.symm.surjective`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced _`.
-/
theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{0}} (Z : Closeds X)
    (h : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have hr : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  haveI : IrreducibleSpace (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    Subtype.irreducibleSpace (by rw [hr]; exact h)
  let f := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Function.Surjective.irreducibleSpace f.symm.continuous f.symm.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced _

open TopologicalSpace in

/- English proof (translation)
Introduce `X _`. Use `haveI : Finite (irreducibleComponents X) := (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype`. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin (irreducibleComponents X)`. Set `C : Fin n → Closeds X` to `fun i => ⟨(e.symm i).1, isClosed_of_mem_irreducibleComponents _ (e.symm i).2⟩`. Use `⟨n, fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subscheme, fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subschemeι, fun i => ⟨GlobalTheory.CompanionTheory.Ar.Approx.isIntegral_subscheme_vanishingIdeal (C i) (e.symm i).2.1, inferInstance⟩, fun x => ⟨e ⟨irreducib …` and prove the remaining obligations.

Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Use `show x ∈ (e.symm (e _)).1`. Rewrite using `[Equiv.symm_apply_apply]`. Conclude with `mem_irreducibleComponent`.
-/
theorem exists_integral_closed_cover :
    ∀ (X : Scheme.{0}) [IsNoetherian X], ∃ (n : ℕ) (Z : Fin n → Scheme.{0}) (j : ∀ i, Z i ⟶ X),
      (∀ i, IsIntegral (Z i) ∧ IsClosedImmersion (j i)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (j i) := by
  intro X _
  haveI : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents X)
  let C : Fin n → Closeds X := fun i =>
    ⟨(e.symm i).1, isClosed_of_mem_irreducibleComponents _ (e.symm i).2⟩
  refine ⟨n, fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subscheme,
    fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subschemeι,
    fun i => ⟨GlobalTheory.CompanionTheory.Ar.Approx.isIntegral_subscheme_vanishingIdeal (C i) (e.symm i).2.1, inferInstance⟩,
    fun x => ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  show x ∈ (e.symm (e _)).1
  rw [Equiv.symm_apply_apply]
  exact mem_irreducibleComponent

end GlobalTheory.CompanionTheory.Ar.Approx
