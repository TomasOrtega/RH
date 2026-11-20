import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInter
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLeftQuotientCovolumeEqFundamentalDomainInter.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter : ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund A : Set I.GA), I.IsFundDom (I.muA μf) fund → MeasurableSet A → (∀ γ ∈ I.GFset, ∀ x ∈ A, γ * x ∈ A) → covol I.GFset (I.muA μf) A = I.muA μf (A ∩ fund) ∧ 0 < I.muA μf fund := by
  first | exact @GlobalTheory.CovolRat.covol_eq_inter_fund | exact GlobalTheory.CovolRat.covol_eq_inter_fund | (intros; apply GlobalTheory.CovolRat.covol_eq_inter_fund <;> assumption)
