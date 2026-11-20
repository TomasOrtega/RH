import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsUniqueEmbeddingReadsGaloisElement.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.existsUnique_embeddingReadsGaloisElement : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  first | exact @GlobalTheory.HTW.Rec.existsUnique_reads | exact GlobalTheory.HTW.Rec.existsUnique_reads | (intros; apply GlobalTheory.HTW.Rec.existsUnique_reads <;> assumption)
