import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubicalOfGroupSchemeIso
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsAmpleCubicalOfGroupSchemeIso.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.exists_ampleCubical_of_groupScheme_iso : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (e : G ≅ G'), IsMonHom e.hom → ∀ L' : LB G'.left, AmpleCub G' L' → ∃ L : LB G.left, AmpleCub G L := by
  first | exact @GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso | exact GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso | (intros; apply GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso <;> assumption)
