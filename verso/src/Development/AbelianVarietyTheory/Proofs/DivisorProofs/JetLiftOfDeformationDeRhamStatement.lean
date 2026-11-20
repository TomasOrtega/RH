import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetLiftOfDeformationDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJetLiftOfDeformationDeRham.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.jet_lift_of_deformation_de_rham : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → JetLift := by
  first | exact @GlobalTheory.LatJet.jetLift_of_deformation_of_deRham | exact GlobalTheory.LatJet.jetLift_of_deformation_of_deRham | (intros; apply GlobalTheory.LatJet.jetLift_of_deformation_of_deRham <;> assumption)
