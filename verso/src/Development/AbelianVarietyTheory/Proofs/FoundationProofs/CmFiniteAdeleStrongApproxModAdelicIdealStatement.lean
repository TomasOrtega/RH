import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCmFiniteAdeleStrongApproxModAdelicIdeal.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.cmFiniteAdele_strong_approx_mod_adelicIdeal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → (∀ (y : AE D) (m : ℕ), 0 < m → ∃ e : D.host.E, ∃ t ∈ IhE D cc, inc D e - y = (m : AE D) * t) ∧ (∀ y : AE D, ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D) ∧ (∀ s ∈ OhE D, ∀ t ∈ IhE D cc, s * t ∈ IhE D cc) := by
  first | exact @GlobalTheory.AdelicApprox.approx_mod_ideal | exact GlobalTheory.AdelicApprox.approx_mod_ideal | (intros; apply GlobalTheory.AdelicApprox.approx_mod_ideal <;> assumption)
