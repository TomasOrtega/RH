import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsHypothesesOfLiterature
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalLanglandsHypothesesOfLiterature.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.local_langlands_hypotheses_of_literature : LitNE → GlobalTheory.NRows.HypothesesX → HypE ∧ PrN ∧ SerN ∧ ∃ hL : GlobalTheory.Published.LocalLanglandsGL, HypN hL := by
  first | exact @GlobalTheory.MemberClose.hyps_of_litNE | exact GlobalTheory.MemberClose.hyps_of_litNE | (intros; apply GlobalTheory.MemberClose.hyps_of_litNE <;> assumption)
