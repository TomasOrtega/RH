import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaximumPrincipleIsotropicFlowRescaledBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMaximumPrincipleIsotropicFlowRescaledBound.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.maximum_principle_isotropicFlow_rescaledBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (w : ℝ), X.IsSec la P → FreqNonneg X la P → (∀ τ, X.spread la τ / 2 ≤ w) → StepBound X w (X.pnorm la P) := by
  first | exact @GlobalTheory.CuspStep.stepBound | exact GlobalTheory.CuspStep.stepBound | (intros; apply GlobalTheory.CuspStep.stepBound <;> assumption)
