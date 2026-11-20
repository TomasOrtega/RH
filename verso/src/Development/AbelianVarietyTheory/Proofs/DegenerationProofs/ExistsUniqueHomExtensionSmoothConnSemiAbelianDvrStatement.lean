import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
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
Apply `GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsUniqueHomExtensionSmoothConnSemiAbelianDvr.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.existsUnique_hom_extension_smoothConn_semiAbelian_dvr : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (H G : Over (Sp T)) [GrpObj H] [GrpObj G], SmConn H → IsSemiAbelian G → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj H ⟶ (Over.pullback (spMap (algebraMap T K))).obj G, IsMonHom f → ∃! F : H ⟶ G, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f := by
  first | exact @GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr | exact GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr | (intros; apply GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr <;> assumption)
