import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPoints
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HubFon.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdmFonOfPoints.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.admFon_of_points : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ := by
  first | exact @GlobalTheory.HubFon.main | exact GlobalTheory.HubFon.main | (intros; apply GlobalTheory.HubFon.main <;> assumption)
