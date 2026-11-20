import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingModHighDegreeProperty
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilRingModHighDegreeProperty.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.breuilRing_mod_high_degree_property : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.RingModHigh O K l e := by
  first | exact @GlobalTheory.BK.ringModHigh | exact GlobalTheory.BK.ringModHigh | (intros; apply GlobalTheory.BK.ringModHigh <;> assumption)
