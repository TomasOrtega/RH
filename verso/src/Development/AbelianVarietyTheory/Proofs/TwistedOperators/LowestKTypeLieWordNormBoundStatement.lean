import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeLieWordNormBound
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepReal.lieBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLowestKTypeLieWordNormBound.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.lowestKType_lieWord_normBound : LieBound := by
  first | exact @GlobalTheory.SepReal.lieBound | exact GlobalTheory.SepReal.lieBound | (intros; apply GlobalTheory.SepReal.lieBound <;> assumption)
