import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTraceCoefficientsNonvanishing
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ProperDenom.exists_local_denom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsOpenTraceCoefficientsNonvanishing.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_open_trace_coefficients_nonvanishing : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] [IsProper f] [IsLocallyNoetherian W] (L : LB M), IsAmpleLB L → ∀ {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) → ∀ y : W, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧ ∀ y' ∈ V, ∀ (V' : W.Opens), y' ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y' (fnOf V (gen_mem hy) d * co j (fnOf (f ⁻¹ᵁ V') h z)) := by
  first | exact @GlobalTheory.ProperDenom.exists_local_denom | exact GlobalTheory.ProperDenom.exists_local_denom | (intros; apply GlobalTheory.ProperDenom.exists_local_denom <;> assumption)
