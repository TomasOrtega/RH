import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfType
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEmbTypeUeIffLocalEmbeddingInCMHalfType.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  first | exact @GlobalTheory.TypeUeHalf.main | exact GlobalTheory.TypeUeHalf.main | (intros; apply GlobalTheory.TypeUeHalf.main <;> assumption)
