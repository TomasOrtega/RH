import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the indicated hypotheses using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem chiInv_slash_dg (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ) (hl : 0 < l)
    (hB : ChiInv k N N χ B) : ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  intro γ hγ
  rw [Gamma0_mem] at hγ
  have hdvd : ((N * l : ℕ) : ℤ) ∣ (mat γ 1 0) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  obtain ⟨t, ht⟩ := hdvd
  have hdet : (mat γ).det = 1 := by simp [mat]
  rw [Matrix.det_fin_two] at hdet
  let γ' : SL(2, ℤ) := ⟨!![mat γ 0 0, (l : ℤ) * mat γ 0 1; (N : ℤ) * t, mat γ 1 1], by
    rw [Matrix.det_fin_two_of]; push_cast at ht; rw [ht] at hdet; linear_combination hdet⟩
  have hE : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [γ']
  have hD : (dg l 1).det ≠ 0 := by simp [dg, Matrix.det_fin_two_of]; omega
  have hDpos : 0 < (dg l 1).det := by simp [dg, Matrix.det_fin_two_of]; exact_mod_cast hl
  have hγd : (mat γ).det ≠ 0 := by simp [mat]
  have hEd : (mat γ').det ≠ 0 := by simp [mat]
  have hmul : dg l 1 * mat γ = mat γ' * dg l 1 := by
    push_cast at ht
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [dg, γ', mat, Matrix.mul_apply, Fin.sum_univ_two, ht] <;> ring
  have hs : mat γ' 1 1 = mat γ 1 1 := rfl
  rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hD hγd, hmul, toGL_mul _ _ hEd hD,
    SlashAction.slash_mul, ← slash_SL_eq, hB γ' hE, smul_slash_toGL k _ hDpos, hs]

end GlobalTheory.HeckeFamilyMatrices
