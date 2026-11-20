import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnipotentUpperSizeReduction
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.unipotent_size_reduction` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FUnipotentUpperSizeReduction.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.unipotent_upper_size_reduction : ∀ (N : ℕ) (n : Matrix (Fin N) (Fin N) ℝ), (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → ∃ ν : Matrix (Fin N) (Fin N) ℤ, (∀ i, ν i i = 1) ∧ (∀ i j, j < i → ν i j = 0) ∧ ∀ i j, i < j → |(n * ν.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by
  first | exact @GlobalTheory.ClassFin.unipotent_size_reduction | exact GlobalTheory.ClassFin.unipotent_size_reduction | (intros; apply GlobalTheory.ClassFin.unipotent_size_reduction <;> assumption)
