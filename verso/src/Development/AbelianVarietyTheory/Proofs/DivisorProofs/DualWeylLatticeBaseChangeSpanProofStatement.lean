import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualWeylLatticeBaseChangeSpanProof.lean&line=182#L182)
-/
theorem _root_.GlobalTheory.T.dualWeylLattice_baseChange_span_proof : GlobalTheory.BaseCmp.NabBaseChange := by
  first | exact @GlobalTheory.NabBC.nabBaseChange | exact GlobalTheory.NabBC.nabBaseChange | (intros; apply GlobalTheory.NabBC.nabBaseChange <;> assumption)
