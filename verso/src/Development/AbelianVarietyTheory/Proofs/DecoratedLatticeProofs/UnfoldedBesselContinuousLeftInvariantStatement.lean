import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselContinuousLeftInvariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Unf.FB.unfF_continuous_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FUnfoldedBesselContinuousLeftInvariant.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.unfoldedBessel_continuous_leftInvariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → Continuous (unfF s vL Y G Φ) ∧ ∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, unfF s vL Y G Φ (γ * h) = unfF s vL Y G Φ h := by
  first | exact @GlobalTheory.Unf.FB.unfF_continuous_invariant | exact GlobalTheory.Unf.FB.unfF_continuous_invariant | (intros; apply GlobalTheory.Unf.FB.unfF_continuous_invariant <;> assumption)
