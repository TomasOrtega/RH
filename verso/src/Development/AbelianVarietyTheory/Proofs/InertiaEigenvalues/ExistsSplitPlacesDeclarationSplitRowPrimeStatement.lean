import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitDecl.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsSplitPlacesDeclarationSplitRowPrime.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  first | exact @GlobalTheory.SplitDecl.main | exact GlobalTheory.SplitDecl.main | (intros; apply GlobalTheory.SplitDecl.main <;> assumption)
