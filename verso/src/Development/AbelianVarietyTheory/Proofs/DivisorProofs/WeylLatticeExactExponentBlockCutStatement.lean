import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCut
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.TailInequalityEventually
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeylLatticeExactExponentBlockCut.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.weylLattice_exact_exponent_block_cut : Formalism.CohomologicalDescent.E.ExCut := by
  first | exact @GlobalTheory.LeviCut.exCut | exact GlobalTheory.LeviCut.exCut | (intros; apply GlobalTheory.LeviCut.exCut <;> assumption)
