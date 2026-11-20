import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOver
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCompletionComparisonAdmissibleEveryPlaceOver.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.completion_comparison_admissible_every_place_over : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i := by
  first | exact @GlobalTheory.BridgeTie.localCoefficientCompatibility | exact GlobalTheory.BridgeTie.localCoefficientCompatibility | (intros; apply GlobalTheory.BridgeTie.localCoefficientCompatibility <;> assumption)
