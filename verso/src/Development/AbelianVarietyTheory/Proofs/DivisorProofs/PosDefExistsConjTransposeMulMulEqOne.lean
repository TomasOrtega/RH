import Mathlib
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory

open Matrix

/- English proof (translation)
Introduce `d H hP`. Establish `hH : H.IsHermitian` using `hP.isHermitian`. Use `set U : Matrix (Fin d) (Fin d) ℂ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef`. Establish `hU1 : Uᴴ * U = 1` using `hH.eigenvectorUnitary.2.1`. Establish `hU2 : U * Uᴴ = 1` using `hH.eigenvectorUnitary.2.2`.

Establish `hspec : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ`. Establish `h` using `hH.spectral_theorem`. Rewrite `h` using `[Unitary.conjStarAlgAut_apply]`. Simplify `h` using `[Matrix.star_eq_conjTranspose, Function.comp_def]`. Establish `hpos : ∀ i, 0 < hH.eigenvalues i` using `fun i => hP.eigenvalues_pos i`.

Set `r : Fin d → ℝ` to `fun i => Real.sqrt (hH.eigenvalues i)`. Establish `hr : ∀ i, 0 < r i` using `fun i => Real.sqrt_pos.2 (hpos i)`. Establish `hrr : ∀ i, r i * r i = hH.eigenvalues i` using `fun i => Real.mul_self_sqrt (hpos i).le`. Set `s : Fin d → ℂ` to `fun i => (((r i)⁻¹ : ℝ) : ℂ)`. Set `t : Fin d → ℂ` to `fun i => ((r i : ℝ) : ℂ)`.

Establish `hst : diagonal s * diagonal t = 1`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr i).ne', Complex.ofReal_one]`.

Establish `hts : diagonal t * diagonal s = 1`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr i).ne', Complex.ofReal_one]`.

Set `Y : Matrix (Fin d) (Fin d) ℂ` to `U * diagonal s`. Set `Z : Matrix (Fin d) (Fin d) ℂ` to `diagonal t * Uᴴ`. Establish `hYZ : Y * Z = 1`. Simplify using `only [Y, Z]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hst, Matrix.one_mul, hU2]`.

Establish `hZY : Z * Y = 1`. Simplify using `only [Y, Z]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hts]`. Use `⟨⟨Y, Z, hYZ, hZY⟩, ?_⟩` and prove the remaining obligations. Use `show Yᴴ * H * Y = 1`.

Establish `hsH : (diagonal s)ᴴ = diagonal s`. Rewrite using `[diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[s]`.

Establish `hdiag : diagonal s * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * diagonal s = 1`. Rewrite using `[diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [s, ← hrr i, ← Complex.ofReal_mul]`.

Rewrite using `[show (r i)⁻¹ * (r i * r i) * (r i)⁻¹ = ((r i)⁻¹ * r i) * (r i * (r i)⁻¹) by ring, inv_mul_cancel₀ (hr i).ne', mul_inv_cancel₀ (hr i).ne']`. Simplify using the standard rewrite rules. Simplify using `only [Y]`. Rewrite using `[conjTranspose_mul, hsH, hspec]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hU1, Matrix.mul_one, Matrix.mul_one, hdiag]`.
-/
theorem posDef_exists_conjTranspose_mul_mul_eq_one :
    ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef →
      ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  intro d H hP
  have hH : H.IsHermitian := hP.isHermitian
  set U : Matrix (Fin d) (Fin d) ℂ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := hH.eigenvectorUnitary.2.1
  have hU2 : U * Uᴴ = 1 := hH.eigenvectorUnitary.2.2
  have hspec : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hP.eigenvalues_pos i
  let r : Fin d → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (hpos i)
  have hrr : ∀ i, r i * r i = hH.eigenvalues i := fun i => Real.mul_self_sqrt (hpos i).le
  let s : Fin d → ℂ := fun i => (((r i)⁻¹ : ℝ) : ℂ)
  let t : Fin d → ℂ := fun i => ((r i : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr i).ne', Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr i).ne', Complex.ofReal_one]
  let Y : Matrix (Fin d) (Fin d) ℂ := U * diagonal s
  let Z : Matrix (Fin d) (Fin d) ℂ := diagonal t * Uᴴ
  have hYZ : Y * Z = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hst, Matrix.one_mul, hU2]
  have hZY : Z * Y = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hts]
  refine ⟨⟨Y, Z, hYZ, hZY⟩, ?_⟩
  show Yᴴ * H * Y = 1
  have hsH : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]
    congr 1; funext i
    simp [s]
  have hdiag : diagonal s * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, ← hrr i, ← Complex.ofReal_mul]
    rw [show (r i)⁻¹ * (r i * r i) * (r i)⁻¹ = ((r i)⁻¹ * r i) * (r i * (r i)⁻¹) by ring,
      inv_mul_cancel₀ (hr i).ne', mul_inv_cancel₀ (hr i).ne']
    simp
  simp only [Y]
  rw [conjTranspose_mul, hsH, hspec]
  calc diagonal s * Uᴴ * (U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal s)
      = diagonal s * (Uᴴ * U) * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal s := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU1, Matrix.mul_one, Matrix.mul_one, hdiag]

end GlobalTheory
