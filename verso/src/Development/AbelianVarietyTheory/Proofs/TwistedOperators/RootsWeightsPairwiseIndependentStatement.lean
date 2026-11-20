import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootsWeightsPairwiseIndependent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Chamber.NonProp.nonprop` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRootsWeightsPairwiseIndependent.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.roots_weights_pairwise_independent : ∀ {k : ℕ} {Q S : Finset (SV k)}, IsPar Q → S ⊆ Q →
  (∀ v ∈ S, ∀ v' ∈ S, v ≠ v' → ∀ r : ℝ, rt S v' ≠ r • rt S v) ∧
  (∀ v ∈ Q \ S, ∀ v' ∈ Q \ S, v ≠ v' → ∀ r : ℝ, wt S v' ≠ r • wt S v) ∧
  (∀ v ∈ Q \ S, ∀ v' ∈ S, ∀ r : ℝ, rt S v' ≠ r • wt S v ∧ wt S v ≠ r • rt S v') := by
  first | exact @GlobalTheory.Chamber.NonProp.nonprop | exact GlobalTheory.Chamber.NonProp.nonprop | (intros; apply GlobalTheory.Chamber.NonProp.nonprop <;> assumption)
