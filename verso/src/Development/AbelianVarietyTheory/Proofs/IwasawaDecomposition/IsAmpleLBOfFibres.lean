import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.AmpleFibres

/- English proof (translation)
Establish `hφ : (pullbackRestrictIsoRestrict B.hom U).inv ≫ pullback.fst B.hom U.ι = (B.hom ⁻¹ᵁ U).ι` using `pullbackRestrictIsoRestrict_inv_fst B.hom U`. Establish `hsq : IsPullback (pullbackRestrictIsoRestrict B.hom U).inv (Over.mk (B.hom ∣_ U)).hom ((Over.pullback U.ι).obj B).hom (𝟙 U.toScheme)`. Use `IsPullback.of_horiz_isIso ⟨?_⟩` and prove the remaining obligations. Simplify using `[← pullbackRestrictIsoRestrict_hom_morphismRestrict]`. Establish `hL₁ : (L.pull (pullback.fst B.hom U.ι)).IsLB` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _`.

Establish `hL₂ : (L.pull (B.hom ⁻¹ᵁ U).ι).IsLB` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _`. Establish `hw : LBIso (L.pull (B.hom ⁻¹ᵁ U).ι) ((L.pull (pullback.fst B.hom U.ι)).pull (pullbackRestrictIsoRestrict B.hom U).inv)`. Conclude with `GenSpread.lbIso_pull_pull hL (pullbackRestrictIsoRestrict B.hom U).inv hφ.symm`. Conclude with `GlobalTheory.AmpleLocalBase.relAmple_baseChange hsq hL₁ hL₂ hw h`.
-/
theorem relAmple_restrict {S : Scheme.{0}} (U : S.Opens) [IsAffine U.toScheme] (B : Over S) {L : LB B.left}
    (hL : L.IsLB)
    (h : ReciprocityTheory.ChartRestriction.G.Out.RelAmple ((Over.pullback U.ι).obj B) (L.pull (pullback.fst B.hom U.ι))) :
    ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk (B.hom ∣_ U)) (L.pull (B.hom ⁻¹ᵁ U).ι) := by
  have hφ : (pullbackRestrictIsoRestrict B.hom U).inv ≫ pullback.fst B.hom U.ι = (B.hom ⁻¹ᵁ U).ι :=
    pullbackRestrictIsoRestrict_inv_fst B.hom U
  have hsq : IsPullback (pullbackRestrictIsoRestrict B.hom U).inv (Over.mk (B.hom ∣_ U)).hom
      ((Over.pullback U.ι).obj B).hom (𝟙 U.toScheme) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    simp [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  have hL₁ : (L.pull (pullback.fst B.hom U.ι)).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hL₂ : (L.pull (B.hom ⁻¹ᵁ U).ι).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hw : LBIso (L.pull (B.hom ⁻¹ᵁ U).ι)
      ((L.pull (pullback.fst B.hom U.ι)).pull (pullbackRestrictIsoRestrict B.hom U).inv) := by
    exact GenSpread.lbIso_pull_pull hL (pullbackRestrictIsoRestrict B.hom U).inv hφ.symm
  exact GlobalTheory.AmpleLocalBase.relAmple_baseChange hsq hL₁ hL₂ hw h

end GlobalTheory.AmpleFibres
