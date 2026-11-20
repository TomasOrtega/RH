import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecomposition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AmbBlockDecomp.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAmbientJumpBlockOfAdmissibleDecomposition.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  first | exact @GlobalTheory.AmbBlockDecomp.main | exact GlobalTheory.AmbBlockDecomp.main | (intros; apply GlobalTheory.AmbBlockDecomp.main <;> assumption)
