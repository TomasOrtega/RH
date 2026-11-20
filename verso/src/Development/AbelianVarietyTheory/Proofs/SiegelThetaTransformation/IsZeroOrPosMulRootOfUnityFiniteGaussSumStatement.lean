import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsZeroOrPosMulRootOfUnityFiniteGaussSum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Phase.GaussSum.ph_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FIsZeroOrPosMulRootOfUnityFiniteGaussSum.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  first | exact @GlobalTheory.Phase.GaussSum.ph_sum | exact GlobalTheory.Phase.GaussSum.ph_sum | (intros; apply GlobalTheory.Phase.GaussSum.ph_sum <;> assumption)
