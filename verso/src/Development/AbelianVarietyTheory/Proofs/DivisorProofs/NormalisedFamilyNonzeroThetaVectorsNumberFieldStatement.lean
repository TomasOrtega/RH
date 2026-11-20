import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ColNorms.familyVectors | exact GlobalTheory.ColNorms.familyVectors | (intros; apply GlobalTheory.ColNorms.familyVectors <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.normalisedFamily_nonzeroThetaVectors_numberField : GlobalTheory.ColNorms.FamilyVectors := by
  first | exact @GlobalTheory.ColNorms.familyVectors | exact GlobalTheory.ColNorms.familyVectors | (intros; apply GlobalTheory.ColNorms.familyVectors <;> assumption)
