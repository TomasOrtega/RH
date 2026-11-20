import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrime
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAmbientTypeConjugatePlaceAtSplitPrime.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.ambientType_conjugatePlace_at_splitPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  first | exact @GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | exact GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | (intros; apply GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow <;> assumption)
