import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSeriesOfReciprocityHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfPowEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SerRefPt.serRef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalSeriesOfReciprocityHypotheses.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.rational_series_of_reciprocity_hypotheses : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.BigOn.Exp.SerRef := by
  first | exact @GlobalTheory.SerRefPt.serRef | exact GlobalTheory.SerRefPt.serRef | (intros; apply GlobalTheory.SerRefPt.serRef <;> assumption)
