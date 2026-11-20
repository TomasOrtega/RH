import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpacePointOfUnitCoordinate
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsProjectiveSpacePointOfUnitCoordinate.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_projectiveSpace_point_of_unit_coordinate : ∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (β : o →+* R) (v : Fin (n + 1) → R), (∃ j, IsUnit (v j)) → ∃ ξ : Sp R ⟶ PSpace o n, ξ ≫ PSpace.str o n = spMap β ∧ PCrd ξ v := by
  first | exact @GlobalTheory.UMin.exists_pCrd_of_isUnit | exact GlobalTheory.UMin.exists_pCrd_of_isUnit | (intros; apply GlobalTheory.UMin.exists_pCrd_of_isUnit <;> assumption)
