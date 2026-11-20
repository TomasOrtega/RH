import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspace
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsRatIdempotentOfAutStableSubspace.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) → ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  first | exact @GlobalTheory.ClassFin.exists_rat_idempotent_of_stable | exact GlobalTheory.ClassFin.exists_rat_idempotent_of_stable | (intros; apply GlobalTheory.ClassFin.exists_rat_idempotent_of_stable <;> assumption)
