import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnrami
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.Rec.existsUnique_over` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsUniqueEmbeddingRestrictsToWachLetterUnrami.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL), K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  first | exact @GlobalTheory.HTW.Rec.existsUnique_over | exact GlobalTheory.HTW.Rec.existsUnique_over | (intros; apply GlobalTheory.HTW.Rec.existsUnique_over <;> assumption)
