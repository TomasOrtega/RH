import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroOfHoweUnramified
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTypeNonzeroOfHoweUnramified.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.type_nonzero_of_howe_unramified : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.NRows.HypothesesX → ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  first | exact @GlobalTheory.DownLift.AtReal.main | exact GlobalTheory.DownLift.AtReal.main | (intros; apply GlobalTheory.DownLift.AtReal.main <;> assumption)
