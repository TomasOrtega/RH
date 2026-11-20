import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

/- English proof (translation)
Introduce `γ hγ`. Rewrite `hγ` using `[Gamma0_mem]`. Establish `hdvd : ((N * l : ℕ) : ℤ) ∣ (mat γ 1 0)` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ`. Take `⟨t, ht⟩` from `hdvd`. Establish `hdet : (mat γ).det = 1` using `by simp [mat]`.

Rewrite `hdet` using `[Matrix.det_fin_two]`. Set `γ' : SL(2, ℤ)` to `⟨!![mat γ 0 0, (l : ℤ) * mat γ 0 1; (N : ℤ) * t, mat γ 1 1], by`. Rewrite using `[Matrix.det_fin_two_of]`. Move the coercions through the operations in `at ht`. Rewrite `hdet` using `[ht]`.

Take the linear combination `hdet⟩`. Establish `hE : γ' ∈ Gamma0 N`. Rewrite using `[Gamma0_mem]`. Simplify using `[γ']`. Establish `hD : (dg l 1).det ≠ 0` using `by simp [dg, Matrix.det_fin_two_of]; omega`.

Establish `hDpos : 0 < (dg l 1).det` using `by simp [dg, Matrix.det_fin_two_of]; exact_mod_cast hl`. Establish `hγd : (mat γ).det ≠ 0` using `by simp [mat]`. Establish `hEd : (mat γ').det ≠ 0` using `by simp [mat]`. Establish `hmul : dg l 1 * mat γ = mat γ' * dg l 1`. Move the coercions through the operations in `at ht`.

Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [dg, γ', mat, Matrix.mul_apply, Fin.sum_univ_two, ht] <;> ring`. Establish `hs : mat γ' 1 1 = mat γ 1 1` using `rfl`. Rewrite using `[slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hD hγd, hmul, toGL_mul _ _ hEd hD, SlashAction.slash_mul, ← slash_SL_eq, hB γ' hE, smul_slash_toGL k _ hDpos, hs]`.
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
