import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.uniqGap_and_besselOfW` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBesselMultiplicityOneLargeGapAndWhittakerBessel.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel : GlobalTheory.GapIn.UniqGap ∧ Formalism.L2.SG.LocWSOf.BesselOfW := by
  first | exact @GlobalTheory.uniqGap_and_besselOfW | exact GlobalTheory.uniqGap_and_besselOfW | (intros; apply GlobalTheory.uniqGap_and_besselOfW <;> assumption)
