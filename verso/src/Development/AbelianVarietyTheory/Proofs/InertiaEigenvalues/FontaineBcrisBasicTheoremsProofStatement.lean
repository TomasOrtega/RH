import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProof
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.fontaineBcris` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFontaineBcrisBasicTheoremsProof.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.fontaineBcrisBasicTheorems_proof : GlobalTheory.Published.FontaineBcris := by
  first | exact @GlobalTheory.MemLoc.fontaineBcris | exact GlobalTheory.MemLoc.fontaineBcris | (intros; apply GlobalTheory.MemLoc.fontaineBcris <;> assumption)
