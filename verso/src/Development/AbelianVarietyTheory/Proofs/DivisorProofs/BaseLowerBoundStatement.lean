import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBound
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.baseGe_of` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBaseLowerBound.lean&line=182#L182)
-/
theorem _root_.GlobalTheory.T.base_lower_bound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → BaseGe := by
  first | exact @GlobalTheory.BigOn.Exp.baseGe_of | exact GlobalTheory.BigOn.Exp.baseGe_of | (intros; apply GlobalTheory.BigOn.Exp.baseGe_of <;> assumption)
