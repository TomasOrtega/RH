import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeWindowEnds
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FMaxSizeAtNonThickPlaceLeWindowEnds.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds : ∀ {D : D7} (L : SizeData₂ D), (wMax D : ℝ) ≤ wB L ∧ (wHat D : ℝ) ≤ wP L := by
  first | exact @GlobalTheory.HTW.Rec.wMax_le_wB | exact GlobalTheory.HTW.Rec.wMax_le_wB | (intros; apply GlobalTheory.HTW.Rec.wMax_le_wB <;> assumption)
