import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UU.fe_all_degrees` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FFunctionalEquationAllDegreesAlgebraicClosure.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.functional_equation_all_degrees_algebraic_closure : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  first | exact @GlobalTheory.UU.fe_all_degrees | exact GlobalTheory.UU.fe_all_degrees | (intros; apply GlobalTheory.UU.fe_all_degrees <;> assumption)
