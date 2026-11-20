import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaRefinementProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ColNorms.coset_refinement | exact GlobalTheory.ColNorms.coset_refinement | (intros; apply GlobalTheory.ColNorms.coset_refinement <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cosetIndicatorThetaRefinement_proof : GlobalTheory.ColNorms.CosetRefinement := by
  first | exact @GlobalTheory.ColNorms.coset_refinement | exact GlobalTheory.ColNorms.coset_refinement | (intros; apply GlobalTheory.ColNorms.coset_refinement <;> assumption)
