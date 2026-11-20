import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogFreeZeroDensityDirichletOneModulus
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FLogFreeZeroDensityDirichletOneModulus.lean&line=322#L322)
-/
theorem _root_.GlobalTheory.T.logFree_zeroDensity_dirichlet_one_modulus : ∃ A C η : ℝ, 0 < A ∧ 0 < C ∧ 0 < η ∧ ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 - η ≤ σ → σ ≤ 1 → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) := by
  first | exact @GlobalTheory.Lin.LogFree.zero_density | exact GlobalTheory.Lin.LogFree.zero_density | (intros; apply GlobalTheory.Lin.LogFree.zero_density <;> assumption)
