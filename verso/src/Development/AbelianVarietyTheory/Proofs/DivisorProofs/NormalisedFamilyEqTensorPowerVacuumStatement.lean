import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormalisedFamilyEqTensorPowerVacuum.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum : GlobalTheory.ColNorms.FamilyTie := by
  first | exact @GlobalTheory.FamilyTieProof.familyTie | exact GlobalTheory.FamilyTieProof.familyTie | (intros; apply GlobalTheory.FamilyTieProof.familyTie <;> assumption)
