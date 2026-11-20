import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylFieldSmul
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Alc.gel_dualWeyl_field` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FTraceRowOperatorPowerDualWeylFieldSmul.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ j : ℕ, ∀ f ∈ dualWeyl k N N ν, gel k N N j f = hcVal k (fun i => (ν i : k)) j • f := by
  first | exact @GlobalTheory.Alc.gel_dualWeyl_field | exact GlobalTheory.Alc.gel_dualWeyl_field | (intros; apply GlobalTheory.Alc.gel_dualWeyl_field <;> assumption)
