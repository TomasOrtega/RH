import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DotDualSubDegreeAnnihilator
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FDotDualSubDegreeAnnihilator.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.dot_dual_sub_degree_annihilator : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth <;> assumption)
