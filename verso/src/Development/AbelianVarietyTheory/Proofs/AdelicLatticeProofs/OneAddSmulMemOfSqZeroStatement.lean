import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneAddSmulMemOfSqZero
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FOneAddSmulMemOfSqZero.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.one_add_smul_mem_of_sq_zero' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → ∀ ε : Matrix ι ι ℂ, ε * ε = 0 → 1 + ε ∈ Γ → ∀ t : ℂ, 1 + t • ε ∈ Γ := by
  first | exact @GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero | exact GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero | (intros; apply GlobalTheory.ClassFin.one_add_smul_mem_of_sq_zero <;> assumption)
