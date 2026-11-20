import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModel
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsWeakNeronModel.lean&line=254#L254)
-/
theorem _root_.GlobalTheory.T.exists_weak_neron_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  first | exact @GlobalTheory.SS.WeakNeronEx.exists_weakNeron | exact GlobalTheory.SS.WeakNeronEx.exists_weakNeron | (intros; apply GlobalTheory.SS.WeakNeronEx.exists_weakNeron <;> assumption)
