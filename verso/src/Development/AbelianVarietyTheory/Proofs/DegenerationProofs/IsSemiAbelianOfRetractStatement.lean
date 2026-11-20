import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetract
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FIsSemiAbelianOfRetract.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.isSemiAbelian_of_retract' : ∀ (S : Scheme.{0}) (G G₁ : Over S) [GrpObj G] [GrpObj G₁], IsSemiAbelian G → SmConn G₁ → ∀ (i : G₁ ⟶ G) (r : G ⟶ G₁), IsMonHom r → i ≫ r = 𝟙 G₁ → IsSemiAbelian G₁ := by
  first | exact @GlobalTheory.SS.isSemiAbelian_of_retract | exact GlobalTheory.SS.isSemiAbelian_of_retract | (intros; apply GlobalTheory.SS.isSemiAbelian_of_retract <;> assumption)
