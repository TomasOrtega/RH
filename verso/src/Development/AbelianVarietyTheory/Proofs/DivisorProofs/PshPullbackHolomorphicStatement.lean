import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshPullbackHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPshPullbackHolomorphic.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.psh_pullback_holomorphic : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (n : ℕ) (Y : Type)
    [TopologicalSpace Y] (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (P : LocPot X),
    IsPotential A P → IsPsh A P → IsPsh B (P.pullback μ hμ.1) := by
  first | exact @GlobalTheory.PshPull.isPsh_pullback | exact GlobalTheory.PshPull.isPsh_pullback | (intros; apply GlobalTheory.PshPull.isPsh_pullback <;> assumption)
