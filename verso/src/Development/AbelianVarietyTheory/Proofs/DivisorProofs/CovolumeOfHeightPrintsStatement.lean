import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeOfHeightHyp
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NefProd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
open GlobalTheory.CovTop GlobalTheory.BigTop
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCovolumeOfHeightHyp.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.covolume_of_height : Slim → HypothesesXH → (∃ r, GlobalTheory.CovTest.Ch2Const r) → CovolX := by
  first | exact @GlobalTheory.CovTop.covolX_of_slim | exact GlobalTheory.CovTop.covolX_of_slim | (intros; apply GlobalTheory.CovTop.covolX_of_slim <;> assumption)
