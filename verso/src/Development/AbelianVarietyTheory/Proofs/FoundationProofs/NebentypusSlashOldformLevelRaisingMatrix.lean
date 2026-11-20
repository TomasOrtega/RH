import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wConjMat (N l a b p q t s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![l * b * p + a * b * (N * l * t) - N * l * q - N * a * s, -a * p - a ^ 2 * N * t + l * q + a * s;
    N * l * (b * p + l * b ^ 2 * t - N * q - b * s), -N * a * p - a * b * (N * l * t) + N * l * q + l * b * s]

/- English proof (translation)
Rewrite using `[wConjMat, Matrix.det_fin_two_of]`. Take the linear combination `(l * b - N * a) ^ 2 * hd + (l * b - N * a + 1) * hab`.
-/
lemma wConjMat_det (N l a b p q t s : ℤ) (hab : l * b - N * a = 1) (hd : p * s - q * (N * l * t) = 1) :
    (wConjMat N l a b p q t s).det = 1 := by
  rw [wConjMat, Matrix.det_fin_two_of]
  linear_combination (l * b - N * a) ^ 2 * hd + (l * b - N * a + 1) * hab

/- English proof (translation)
Rewrite using `[wOld, wConjMat, Matrix.mul_fin_two, Matrix.mul_fin_two]`. Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`. Take the linear combination `(-((l : ℤ) * p + a * (N * l * t))) * hab`.

Take the linear combination `(-((l : ℤ) * q + a * s)) * hab`. Take the linear combination `(-((N : ℤ) * l * p + l * b * (N * l * t))) * hab`. Take the linear combination `(-((N : ℤ) * l * q + l * b * s)) * hab`.
-/
lemma wOld_mul_eq (N l : ℕ) (a b p q t s : ℤ) (hab : (l : ℤ) * b - N * a = 1) :
    wOld N l a b * !![p, q; (N : ℤ) * l * t, s] = wConjMat N l a b p q t s * wOld N l a b := by
  rw [wOld, wConjMat, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-((l : ℤ) * p + a * (N * l * t))) * hab
  · linear_combination (-((l : ℤ) * q + a * s)) * hab
  · linear_combination (-((N : ℤ) * l * p + l * b * (N * l * t))) * hab
  · linear_combination (-((N : ℤ) * l * q + l * b * s)) * hab

/- English proof (translation)
Introduce `N l k a b hab χ G hl hG γ hγ`. Rewrite `hγ` using `[Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Take `⟨t, ht⟩` from `hγ`. Establish `ht' : mat γ 1 0 = (N : ℤ) * l * t` using `by rw [← Nat.cast_mul]; exact ht`. Establish `hm : mat γ = !![mat γ 0 0, mat γ 0 1; (N : ℤ) * l * t, mat γ 1 1]`.

Rewrite using `[← ht']`. Conclude with `Matrix.eta_fin_two _`. Establish `hd : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * ((N : ℤ) * l * t) = 1`. Rewrite using `[← ht', ← Matrix.det_fin_two]`. Conclude with `γ.2`.

Set `δ : SL(2, ℤ)` to `⟨wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1), wConjMat_det _ _ _ _ _ _ _ _ hab hd⟩`. Establish `hδ : mat δ = wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1)` using `rfl`. Establish `key : wOld N l a b * mat γ = mat δ * wOld N l a b`. Rewrite using `[hδ, ← wOld_mul_eq N l a b _ _ t _ hab, ← hm]`. Establish `hW : 0 < (wOld N l a b).det`.

Establish `: (wOld N l a b).det = l`. Rewrite using `[wOld, Matrix.det_fin_two_of]`. Take the linear combination `(l : ℤ) * hab`. Rewrite using `[this]`. Conclude with `hl` after adjusting the coercions.

Establish `h1 : ∀ x : SL(2, ℤ), (mat x).det ≠ 0` using `fun x => by simp [mat]`. Establish `hδ0 : δ ∈ Gamma0 (N * l)`. Rewrite using `[Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `⟨b * mat γ 0 0 + l * b ^ 2 * t - N * mat γ 0 1 - b * mat γ 1 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul]`.

Both sides reduce to the same expression. Establish `h11 : ((mat δ 1 1 : ℤ) : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N)`. Establish `: mat δ 1 1 = mat γ 1 1 + N * (-a * mat γ 0 0 - a * b * l * t + l * mat γ 0 1 + a * mat γ 1 1)`. Establish `e : mat δ 1 1 = -(N : ℤ) * a * mat γ 0 0 - a * b * (N * l * t) + N * l * mat γ 0 1 + l * b * mat γ 1 1` using `rfl`. Rewrite using `[e]`.

Take the linear combination `(mat γ 1 1) * hab`. Rewrite using `[this, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]`. Rewrite using `[slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (h1 γ), key, toGL_mul _ _ (h1 δ) hW.ne', SlashAction.slash_mul, ← slash_SL_eq, hG δ hδ0, smul_slash_toGL k _ hW, h11]`.
-/
theorem chiInv_slash_wOld : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 →
    ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G →
      ChiInv k N (N * l) χ (G ∣[k] toGL (wOld N l a b)) := by
  intro N l k a b hab χ G hl hG γ hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨t, ht⟩ := hγ
  have ht' : mat γ 1 0 = (N : ℤ) * l * t := by rw [← Nat.cast_mul]; exact ht
  have hm : mat γ = !![mat γ 0 0, mat γ 0 1; (N : ℤ) * l * t, mat γ 1 1] := by
    rw [← ht']; exact Matrix.eta_fin_two _
  have hd : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * ((N : ℤ) * l * t) = 1 := by
    rw [← ht', ← Matrix.det_fin_two]; exact γ.2
  let δ : SL(2, ℤ) := ⟨wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1),
    wConjMat_det _ _ _ _ _ _ _ _ hab hd⟩
  have hδ : mat δ = wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1) := rfl
  have key : wOld N l a b * mat γ = mat δ * wOld N l a b := by
    rw [hδ, ← wOld_mul_eq N l a b _ _ t _ hab, ← hm]
  have hW : 0 < (wOld N l a b).det := by
    have : (wOld N l a b).det = l := by
      rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * hab
    rw [this]; exact_mod_cast hl
  have h1 : ∀ x : SL(2, ℤ), (mat x).det ≠ 0 := fun x => by simp [mat]
  have hδ0 : δ ∈ Gamma0 (N * l) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨b * mat γ 0 0 + l * b ^ 2 * t - N * mat γ 0 1 - b * mat γ 1 1, ?_⟩
    rw [Nat.cast_mul]; rfl
  have h11 : ((mat δ 1 1 : ℤ) : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N) := by
    have : mat δ 1 1 = mat γ 1 1 +
        N * (-a * mat γ 0 0 - a * b * l * t + l * mat γ 0 1 + a * mat γ 1 1) := by
      have e : mat δ 1 1 = -(N : ℤ) * a * mat γ 0 0 - a * b * (N * l * t) + N * l * mat γ 0 1 +
        l * b * mat γ 1 1 := rfl
      rw [e]; linear_combination (mat γ 1 1) * hab
    rw [this, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (h1 γ), key,
    toGL_mul _ _ (h1 δ) hW.ne', SlashAction.slash_mul, ← slash_SL_eq, hG δ hδ0,
    smul_slash_toGL k _ hW, h11]

end GlobalTheory.HeckeFamilyMatrices
