import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdeal
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FConjStableInverseDifferentAndNormIdeal.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | exact GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | (intros; apply GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal <;> assumption)
