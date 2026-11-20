import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

open Matrix

namespace GlobalTheory.UnitaryPerturbation

/- English proof (translation)
Use `show (1 + z • (Matrix.vecMulVec v (star v) * Hm))ᴴ * Hm * (1 + z • (Matrix.vecMulVec v (star v) * Hm)) = Hm`. Establish `hHc : Hmᴴ = Hm` using `hH`. Take `⟨M, hMdef⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ, M = Matrix.vecMulVec v (star v)` from `⟨_, rfl⟩`. Take `⟨c, hcdef⟩ : ∃ c : ℂ, c = star v ⬝ᵥ Matrix.mulVec Hm v` from `⟨_, rfl⟩`. Rewrite `hz` using `[← hcdef]`.

Establish `hMc : Mᴴ = M` using `by rw [hMdef, Matrix.conjTranspose_vecMulVec, star_star]`. Establish `hMHM : M * Hm * M = c • M`. Use extensionality with `i j`. Simplify using `only [hMdef, hcdef, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `key : Hm * (M * (Hm * (M * Hm))) = c • (Hm * (M * Hm))`. Establish `h1 : M * (Hm * (M * Hm)) = c • (M * Hm)`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hMHM, Matrix.smul_mul]`.

Rewrite using `[h1, Matrix.mul_smul]`. Rewrite using `[← hMdef, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hMc, hHc]`. Establish `expand : (1 + star z • (Hm * M)) * Hm * (1 + z • (M * Hm)) = Hm + (star z + z + star z * z * c) • (Hm * (M * Hm))`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]`. Rewrite using `[key]`.

Use `module`. Rewrite using `[expand, hz, zero_smul, add_zero]`.
-/
theorem one_add_smul_mem_unitary {n : ℕ} {Hm : GlobalTheory.HolDict.Mt n} (hH : Matrix.IsHermitian Hm) (v : Fin n → ℂ) (z : ℂ)
    (hz : star z + z + star z * z * star v ⬝ᵥ Matrix.mulVec Hm v = (0 : ℂ)) :
    (1 : Matrix (Fin n) (Fin n) ℂ) + z • (Matrix.vecMulVec v (star v) * Hm) ∈ Formalism.QuantumDeterminants.UH Hm := by
  show (1 + z • (Matrix.vecMulVec v (star v) * Hm))ᴴ * Hm * (1 + z • (Matrix.vecMulVec v (star v) * Hm)) = Hm
  have hHc : Hmᴴ = Hm := hH
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ, M = Matrix.vecMulVec v (star v) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = star v ⬝ᵥ Matrix.mulVec Hm v := ⟨_, rfl⟩
  rw [← hcdef] at hz
  have hMc : Mᴴ = M := by rw [hMdef, Matrix.conjTranspose_vecMulVec, star_star]
  have hMHM : M * Hm * M = c • M := by
    ext i j
    simp only [hMdef, hcdef, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have key : Hm * (M * (Hm * (M * Hm))) = c • (Hm * (M * Hm)) := by
    have h1 : M * (Hm * (M * Hm)) = c • (M * Hm) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMHM, Matrix.smul_mul]
    rw [h1, Matrix.mul_smul]
  rw [← hMdef, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, hMc, hHc]
  have expand : (1 + star z • (Hm * M)) * Hm * (1 + z • (M * Hm)) =
      Hm + (star z + z + star z * z * c) • (Hm * (M * Hm)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc]
    rw [key]
    module
  rw [expand, hz, zero_smul, add_zero]

end GlobalTheory.UnitaryPerturbation
