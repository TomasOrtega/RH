import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainCoverOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransport
open GlobalTheory.ChainPts
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChainCoverOfHyp.lean&line=240#L240)
-/
theorem _root_.GlobalTheory.T.chain_cover_of_hypotheses : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → GlobalTheory.GroupBplus.GroupAllSt → GlobalTheory.ChainPts.ChainCoverSt := by
  first | exact @GlobalTheory.ChainPts.Cover.chainCoverSt | exact GlobalTheory.ChainPts.Cover.chainCoverSt | (intros; apply GlobalTheory.ChainPts.Cover.chainCoverSt <;> assumption)
