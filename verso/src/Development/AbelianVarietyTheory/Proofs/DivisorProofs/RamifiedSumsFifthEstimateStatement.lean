import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimate
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRamifiedSumsFifthEstimate.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.rank_gap_bound' : RankGapBound := by
  first | exact @GlobalTheory.BigTop.Fun.ramified_sums_fifth_bound | exact GlobalTheory.BigTop.Fun.ramified_sums_fifth_bound | (intros; apply GlobalTheory.BigTop.Fun.ramified_sums_fifth_bound <;> assumption)
