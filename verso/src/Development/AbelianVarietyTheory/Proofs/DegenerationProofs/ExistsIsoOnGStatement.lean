import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ex.RecPeriods.exists_iso_onG` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsIsoOnG.lean&line=257#L257)
-/
theorem _root_.GlobalTheory.T.exists_numD_iso_onG_of_allMatch : AllMatch fun {_} _ {N} {N'} {_} μ _ _ => μ.A → ∀ e, μ.B e → μ.Term e → ∀ I : NumB.Iso N.toNumB N'.toNumB, μ.OnB I → ∃ J : NumD.Iso N N', J.toIso = I ∧ J.e = e ∧ μ.OnG J := by
  first | exact @GlobalTheory.Ex.RecPeriods.exists_iso_onG | exact GlobalTheory.Ex.RecPeriods.exists_iso_onG | (intros; apply GlobalTheory.Ex.RecPeriods.exists_iso_onG <;> assumption)
