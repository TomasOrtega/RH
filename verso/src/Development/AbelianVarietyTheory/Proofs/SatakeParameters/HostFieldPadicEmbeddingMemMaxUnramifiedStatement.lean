import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramified
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FHostFieldPadicEmbeddingMemMaxUnramified.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (x : H.E), c x ∈ Loc.MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.HostKur.host_image_mem_Kur | exact GlobalTheory.HostKur.host_image_mem_Kur | (intros; apply GlobalTheory.HostKur.host_image_mem_Kur <;> assumption)
