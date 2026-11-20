import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromHeightTheorems
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesY
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses3
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
open GlobalTheory.CovTop GlobalTheory.BigTop
/- English proof (citation)
Apply `GlobalTheory.CovTop.AllSteps.covolX_of_scholzeWeinstein` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCovolumeFromHeightTheorems.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.covolume_from_height_theorems : HypothesesXH → GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses3 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.CovHt.Known₂ → CovolX := by
  first | exact @GlobalTheory.CovTop.AllSteps.covolX_of_scholzeWeinstein | exact GlobalTheory.CovTop.AllSteps.covolX_of_scholzeWeinstein | (intros; apply GlobalTheory.CovTop.AllSteps.covolX_of_scholzeWeinstein <;> assumption)
