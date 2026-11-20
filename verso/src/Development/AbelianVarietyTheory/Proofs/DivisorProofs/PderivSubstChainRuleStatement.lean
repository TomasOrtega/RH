import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivSubstChainRule
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PSChain.pderiv_subst_chain` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPderivSubstChainRule.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.pderiv_subst_chain_rule : ∀ {R σ τ : Type} [CommRing R] [Fintype σ] [Fintype τ] (a : σ → MvPowerSeries τ R), (∀ s, constantCoeff (a s) = 0) → ∀ (f : MvPowerSeries σ R) (k : τ), pderiv R k (subst a f) = ∑ j, subst a (pderiv R j f) * pderiv R k (a j) := by
  first | exact @GlobalTheory.PSChain.pderiv_subst_chain | exact GlobalTheory.PSChain.pderiv_subst_chain | (intros; apply GlobalTheory.PSChain.pderiv_subst_chain <;> assumption)
