import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyCoefficientFieldEmbeddingPadicComplex
import Mathlib
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FNonemptyCoefficientFieldEmbeddingPadicComplex.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.nonempty_coefficient_field_embedding_padic_complex : ∀ (p : ℕ) [Fact p.Prime] (G : Formalism.MainNotions.G.GAtP p), 0 < G.P.nV → Nonempty (Formalism.L2.G.Pend.CEmb G) := by
  first | exact @GlobalTheory.nonempty_cEmb_of_pos_nV | exact GlobalTheory.nonempty_cEmb_of_pos_nV | (intros; apply GlobalTheory.nonempty_cEmb_of_pos_nV <;> assumption)
