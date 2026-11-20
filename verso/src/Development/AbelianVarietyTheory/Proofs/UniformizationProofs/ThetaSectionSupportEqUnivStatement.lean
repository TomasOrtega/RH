import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UU.theta_support_eq_univ` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FThetaSectionSupportEqUniv.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.thetaSection_support_eq_univ : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ α, U.Supp (Kbar V) 2 α) := by
  first | exact @GlobalTheory.UU.theta_support_eq_univ | exact GlobalTheory.UU.theta_support_eq_univ | (intros; apply GlobalTheory.UU.theta_support_eq_univ <;> assumption)
