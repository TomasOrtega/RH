import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ColNorms.familyVectors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormalisedFamilyNonzeroThetaVectorsNumberField.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.normalisedFamily_nonzeroThetaVectors_numberField : GlobalTheory.ColNorms.FamilyVectors := by
  first | exact @GlobalTheory.ColNorms.familyVectors | exact GlobalTheory.ColNorms.familyVectors | (intros; apply GlobalTheory.ColNorms.familyVectors <;> assumption)
