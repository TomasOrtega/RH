import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCut
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.TailInequalityEventually
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LeviCut.exCut | exact GlobalTheory.LeviCut.exCut | (intros; apply GlobalTheory.LeviCut.exCut <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.weylLattice_exact_exponent_block_cut : Formalism.CohomologicalDescent.E.ExCut := by
  first | exact @GlobalTheory.LeviCut.exCut | exact GlobalTheory.LeviCut.exCut | (intros; apply GlobalTheory.LeviCut.exCut <;> assumption)
