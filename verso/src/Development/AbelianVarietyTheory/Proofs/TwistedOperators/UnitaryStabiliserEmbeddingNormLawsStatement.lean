import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepReal.embLaws` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryStabiliserEmbeddingNormLaws.lean&line=274#L274)
-/
theorem _root_.GlobalTheory.T.unitary_stabiliser_embedding_norm_laws : EmbLaws := by
  first | exact @GlobalTheory.SepReal.embLaws | exact GlobalTheory.SepReal.embLaws | (intros; apply GlobalTheory.SepReal.embLaws <;> assumption)
