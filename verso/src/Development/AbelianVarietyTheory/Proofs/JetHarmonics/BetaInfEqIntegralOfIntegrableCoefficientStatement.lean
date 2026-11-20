import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaInfEqIntegralOfIntegrableCoefficient
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FBetaInfEqIntegralOfIntegrableCoefficient.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.betaInf_eq_integral_of_integrable_coefficient : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 4 F → Integrable (B.Ph D F F) D.μSS → B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS := by
  first | exact @GlobalTheory.RegularisedIntegral.betaInf_eq_integral | exact GlobalTheory.RegularisedIntegral.betaInf_eq_integral | (intros; apply GlobalTheory.RegularisedIntegral.betaInf_eq_integral <;> assumption)
