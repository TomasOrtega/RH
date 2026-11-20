import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.keyFormulaUnitOverNormalBase_of_familyUnit_of_traits : ∀ κ : Rule, FamUnit κ → KeyTrait κ → KeyLoc κ := by
  first | exact @GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait | exact GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait | (intros; apply GlobalTheory.KeyEven.LocPf.keyLoc_of_famUnit_keyTrait <;> assumption)
