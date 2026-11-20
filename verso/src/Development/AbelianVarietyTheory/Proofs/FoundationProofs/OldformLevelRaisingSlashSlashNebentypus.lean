import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul

noncomputable section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wSqOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : SL(2, ℤ) :=
  ⟨!![(l : ℤ) + a * N, a * (1 + b); (N : ℤ) * l * (1 + b), (N : ℤ) * a + l * b ^ 2], by
    rw [Matrix.det_fin_two_of]; linear_combination ((l : ℤ) * b - N * a + 1) * h⟩

/- English proof (translation)
Rewrite using `[wOld, Matrix.det_fin_two_of]`. Take the linear combination `(l : ℤ) * h`.
-/
lemma oldformLevelRaisingMatrix_det_eq_level (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : (wOld N l a b).det = l := by
  rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * h

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [wOld, wSqOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring`.
-/
lemma atkin_lehner_square_mul (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    wOld N l a b * wOld N l a b = (l : ℤ) • mat (wSqOld N l a b h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wOld, wSqOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/- English proof (translation)
Rewrite using `[Gamma0_mem]`. Establish `: ((((wSqOld N l a b h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) = ((N * l : ℕ) : ℤ) * (1 + b)`. Simplify using `[wSqOld]`. Rewrite using `[this, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]`.
-/
lemma wSqOld_mem (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    wSqOld N l a b h ∈ Gamma0 (N * l) := by
  rw [Gamma0_mem]
  have : ((((wSqOld N l a b h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) = ((N * l : ℕ) : ℤ) * (1 + b) := by
    simp [wSqOld]
  rw [this, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

/- English proof (translation)
Establish `e : mat (wSqOld N l a b h) 1 1 = b + (N : ℤ) * (a * (1 + b))`. Simplify using `[wSqOld, mat]`. Take the linear combination `b * h`. Rewrite using `[e]`. Use `push_cast`.

Simplify using the standard rewrite rules.
-/
lemma wSqOld_entry (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    ((mat (wSqOld N l a b h) 1 1 : ℤ) : ZMod N) = (b : ZMod N) := by
  have e : mat (wSqOld N l a b h) 1 1 = b + (N : ℤ) * (a * (1 + b)) := by
    simp [wSqOld, mat]; linear_combination b * h
  rw [e]; push_cast; simp

/- English proof (translation)
Establish `hd : (wOld N l a b).det ≠ 0` using `by rw [oldformLevelRaisingMatrix_det_eq_level N l a b h]; exact_mod_cast hl.ne'`. Establish `hM : 0 < (mat (wSqOld N l a b h)).det` using `by simp [mat]`. Rewrite using `[← SlashAction.slash_mul, ← toGL_mul _ _ hd hd, atkin_lehner_square_mul N l a b h, slash_toGL_smul k l hl _ hM, ← slash_SL_eq, hG _ (wSqOld_mem N l a b h), wSqOld_entry, smul_smul]`.
-/
theorem wOld_slash_slash (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N)
    (G : ℍ → ℂ) (hl : 0 < l) (hG : ChiInv k N (N * l) χ G) :
    (G ∣[k] toGL (wOld N l a b)) ∣[k] toGL (wOld N l a b) = ((l : ℂ) ^ (k - 2) * χ (b : ZMod N)) • G := by
  have hd : (wOld N l a b).det ≠ 0 := by rw [oldformLevelRaisingMatrix_det_eq_level N l a b h]; exact_mod_cast hl.ne'
  have hM : 0 < (mat (wSqOld N l a b h)).det := by simp [mat]
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ hd hd, atkin_lehner_square_mul N l a b h, slash_toGL_smul k l hl _ hM,
    ← slash_SL_eq, hG _ (wSqOld_mem N l a b h), wSqOld_entry, smul_smul]

end GlobalTheory.HeckeFamilyMatrices
