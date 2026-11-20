import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsOpenImmersionQuotient
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

/- English proof (translation)
Introduce `o _ _ X s hs`. Establish `hfin : IsFinite (spMap (Int.castRingHom o))`. Establish `he : Int.castRingHom o = algebraMap ℤ o` using `RingHom.ext_int _ _`. Rewrite using `[he]`. Use `show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℤ o)))`.

Rewrite using `[IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.mpr inferInstance`. Conclude with `GlobalTheory.QuotModel.isProjOver_comp_spMap _ s hfin hs`.
-/
theorem isProjOver_comp_spMap_int : ∀ (o : Type) [CommRing o] [Module.Finite ℤ o] (X : Scheme.{0}) (s : X ⟶ Sp o),
    IsProjOver s → IsProjOver (s ≫ spMap (Int.castRingHom o)) := by
  intro o _ _ X s hs
  have hfin : IsFinite (spMap (Int.castRingHom o)) := by
    have he : Int.castRingHom o = algebraMap ℤ o := RingHom.ext_int _ _
    rw [he]
    show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℤ o)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact GlobalTheory.QuotModel.isProjOver_comp_spMap _ s hfin hs

end GlobalTheory.CompanionTheory.Ar.XR
