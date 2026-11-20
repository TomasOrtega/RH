import Mathlib
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.Unitary.ExpUpper

open scoped Matrix.Norms.L2Operator in

/- English proof (translation)
Establish `hmem : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • T ^ k) ∈ Matrix.blockTriangularSubalgebra ℂ ℂ id` using `fun k => Subalgebra.smul_mem _ (Subalgebra.pow_mem _ ((Matrix.mem_blockTriangularSubalgebra).mpr hT) k) _`. Use `(isClosed_setOfPred_blockTriangular (b := id)).mem_of_tendsto (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (x := T)) (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Conclude with `(Matrix.mem_blockTriangularSubalgebra).mp (Subalgebra.sum_mem _ fun k _ => hmem k)`.
-/
theorem blockTriangular_exp {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.BlockTriangular id) : (NormedSpace.exp T).BlockTriangular id := by
  have hmem : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • T ^ k) ∈ Matrix.blockTriangularSubalgebra ℂ ℂ id := fun k =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ ((Matrix.mem_blockTriangularSubalgebra).mpr hT) k) _

  refine (isClosed_setOfPred_blockTriangular (b := id)).mem_of_tendsto
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (x := T)) (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mem_blockTriangularSubalgebra).mp (Subalgebra.sum_mem _ fun k _ => hmem k)

/- English proof (translation)
Establish `hUU : Uᴴ * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hU`. Establish `hUU' : U * Uᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hU`. Establish `hunit : IsUnit U` using `⟨⟨U, Uᴴ, hUU', hUU⟩, rfl⟩`. Establish `hinv : U⁻¹ = Uᴴ` using `Matrix.inv_eq_left_inv hUU`. Rewrite using `[← hinv, ← Matrix.exp_conj' U Y hunit]`.

Conclude with `GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp _ (hinv ▸ h)`.
-/
theorem blockTriangular_conj_exp {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : (Uᴴ * Y * U).BlockTriangular id) :
    (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU', hUU⟩, rfl⟩
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hUU
  rw [← hinv, ← Matrix.exp_conj' U Y hunit]
  exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp _ (hinv ▸ h)

end GlobalTheory.CompanionTheory.Unitary.ExpUpper
