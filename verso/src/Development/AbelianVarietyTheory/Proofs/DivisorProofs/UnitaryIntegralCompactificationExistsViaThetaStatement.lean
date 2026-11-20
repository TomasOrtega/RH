import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationExistsViaTheta
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
Apply `GlobalTheory.umin_theta_compactification_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryIntegralCompactificationExistsViaTheta.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.unitary_integral_compactification_exists_via_theta : UMinSt := by
  first | exact @GlobalTheory.umin_theta_compactification_exists | exact GlobalTheory.umin_theta_compactification_exists | (intros; apply GlobalTheory.umin_theta_compactification_exists <;> assumption)
