import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EntriesBoundedOfConjSpanningBounded
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FEntriesBoundedOfConjSpanningBounded.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  first | exact @GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | exact GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | (intros; apply GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded <;> assumption)
