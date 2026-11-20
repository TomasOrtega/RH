import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFrameOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOneFormsIsBaseChangeTangentRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentRepresentationSmoothGroupSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R _ A _ hs`. Take `⟨W, i1, i2, hfin, hproj, ⟨t⟩⟩` from `GlobalTheory.T.exists_tangentRepresentation_smooth_groupScheme R A hs`. Take `⟨j, hj⟩` from `GlobalTheory.T.exists_global_oneForms_isBaseChange_tangentRep R A W t`. Conclude with `GlobalTheory.AbCoh.hasFrame_of_isBaseChange R _ (OAff A.hom) W j hj`.
-/
theorem hasFrame_of_smooth_grpObj : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    Smooth A.hom → HasFrame (OAff A.hom) := by
  intro R _ A _ hs
  obtain ⟨W, i1, i2, hfin, hproj, ⟨t⟩⟩ := GlobalTheory.T.exists_tangentRepresentation_smooth_groupScheme R A hs
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_global_oneForms_isBaseChange_tangentRep R A W t
  exact GlobalTheory.AbCoh.hasFrame_of_isBaseChange R _ (OAff A.hom) W j hj

end GlobalTheory.AbCoh
