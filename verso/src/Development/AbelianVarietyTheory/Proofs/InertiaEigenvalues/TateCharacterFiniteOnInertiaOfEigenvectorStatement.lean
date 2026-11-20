import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateCharacterFiniteOnInertiaOfEigenvector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TateEigen.finite_on_inertia` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTateCharacterFiniteOnInertiaOfEigenvector.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.tate_character_finite_on_inertia_of_eigenvector : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (y : ℂ_[l]), y ≠ 0 → (∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y) → ∃ N : ℕ, 0 < N ∧ ∀ γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup, η γ ^ N = 1 := by
  first | exact @GlobalTheory.TateEigen.finite_on_inertia | exact GlobalTheory.TateEigen.finite_on_inertia | (intros; apply GlobalTheory.TateEigen.finite_on_inertia <;> assumption)
