import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorUnramifiedFrobTwistIterateDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPadicTensorUnramifiedFrobTwistIterateDegree.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := by
  first | exact @GlobalTheory.LKRes.sigKQ_iterate_self | exact GlobalTheory.LKRes.sigKQ_iterate_self | (intros; apply GlobalTheory.LKRes.sigKQ_iterate_self; all_goals assumption)
