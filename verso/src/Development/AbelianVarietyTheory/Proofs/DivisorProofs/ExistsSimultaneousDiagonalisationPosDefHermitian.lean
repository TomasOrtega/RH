import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

/- English proof (translation)
Establish `h1 : (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1`. Use `hA.eigenvectorUnitary.2.1` as an intermediate fact. Simplify `this` using `[Matrix.star_eq_conjTranspose]`. Use `⟨hA.eigenvectorUnitary, h1, ?_⟩` and prove the remaining obligations. Establish `h` using `hA.spectral_theorem`.

Rewrite `h` using `[Unitary.conjStarAlgAut_apply]`. Use `set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU`. Use `set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD`. Establish `h2 : Uᴴ * A * U = D`. Rewrite using `[h, Matrix.star_eq_conjTranspose]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, hD]`. Both sides reduce to the same expression.
-/
theorem exists_unitary_conj_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    ∃ U : Matrix ι ι ℂ, Uᴴ * U = 1 ∧
      Uᴴ * A * U = Matrix.diagonal fun i => (hA.eigenvalues i : ℂ) := by
  have h1 : (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    have := hA.eigenvectorUnitary.2.1
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨hA.eigenvectorUnitary, h1, ?_⟩
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have h2 : Uᴴ * A * U = D := by
    rw [h, Matrix.star_eq_conjTranspose]
    calc Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = D := by rw [h1]; simp
  rw [h2, hD]; rfl

/- English proof (translation)
Introduce `ι _ _ G G' hG hG'`. Take `⟨U, hU, hUG⟩` from `exists_unitary_conj_diagonal G hG.1`. Establish `hpos : ∀ i, 0 < hG.1.eigenvalues i` using `hG.eigenvalues_pos`. Use `set S : Matrix ι ι ℂ := Matrix.diagonal fun i => (((Real.sqrt (hG.1.eigenvalues i))⁻¹ : ℝ) : ℂ) with hS`. Establish `hSH : Sᴴ = S`.

Rewrite using `[hS, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `h0 : (U * S)ᴴ * G * (U * S) = 1`.

Establish `: (U * S)ᴴ * G * (U * S) = S * (Uᴴ * G * U) * S`. Rewrite using `[Matrix.conjTranspose_mul, hSH]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, hUG, hS, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Establish `hs : 0 < Real.sqrt (hG.1.eigenvalues i)` using `Real.sqrt_pos.2 (hpos i)`. Establish `hs2` using `Real.mul_self_sqrt (hpos i).le`. Establish `: (Real.sqrt (hG.1.eigenvalues i))⁻¹ * hG.1.eigenvalues i * (Real.sqrt (hG.1.eigenvalues i))⁻¹ = 1`. Clear the denominators using the available nonvanishing facts.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `this` after adjusting the coercions. Establish `hH : ((U * S)ᴴ * G' * (U * S)).IsHermitian` using `Matrix.isHermitian_conjTranspose_mul_mul _ hG'`. Take `⟨V, hV, hVG⟩` from `exists_unitary_conj_diagonal _ hH`. Establish `h1 : (U * S * V)ᴴ * G * (U * S * V) = 1`.

Establish `: (U * S * V)ᴴ * G * (U * S * V) = Vᴴ * ((U * S)ᴴ * G * (U * S)) * V`. Rewrite using `[Matrix.conjTranspose_mul (U * S) V]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, h0, Matrix.mul_one, hV]`. Use `⟨U * S * V, hH.eigenvalues, ?_, h1, ?_⟩` and prove the remaining obligations.

Conclude with `Matrix.isUnit_det_of_left_inverse h1`. Rewrite using `[← hVG, Matrix.conjTranspose_mul (U * S) V]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem simultaneous_diagonalisation :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G G' : Matrix ι ι ℂ), G.PosDef → G'.IsHermitian →
      ∃ (T : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit T.det ∧ Tᴴ * G * T = 1 ∧
        Tᴴ * G' * T = Matrix.diagonal fun i => (d i : ℂ) := by
  intro ι _ _ G G' hG hG'
  obtain ⟨U, hU, hUG⟩ := exists_unitary_conj_diagonal G hG.1
  have hpos : ∀ i, 0 < hG.1.eigenvalues i := hG.eigenvalues_pos
  set S : Matrix ι ι ℂ := Matrix.diagonal fun i => (((Real.sqrt (hG.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
    with hS
  have hSH : Sᴴ = S := by
    rw [hS, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have h0 : (U * S)ᴴ * G * (U * S) = 1 := by
    have : (U * S)ᴴ * G * (U * S) = S * (Uᴴ * G * U) * S := by
      rw [Matrix.conjTranspose_mul, hSH]; simp only [Matrix.mul_assoc]
    rw [this, hUG, hS, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    have hs : 0 < Real.sqrt (hG.1.eigenvalues i) := Real.sqrt_pos.2 (hpos i)
    have hs2 := Real.mul_self_sqrt (hpos i).le
    have : (Real.sqrt (hG.1.eigenvalues i))⁻¹ * hG.1.eigenvalues i *
        (Real.sqrt (hG.1.eigenvalues i))⁻¹ = 1 := by
      field_simp
      nlinarith
    exact_mod_cast this
  have hH : ((U * S)ᴴ * G' * (U * S)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul _ hG'
  obtain ⟨V, hV, hVG⟩ := exists_unitary_conj_diagonal _ hH
  have h1 : (U * S * V)ᴴ * G * (U * S * V) = 1 := by
    have : (U * S * V)ᴴ * G * (U * S * V) = Vᴴ * ((U * S)ᴴ * G * (U * S)) * V := by
      rw [Matrix.conjTranspose_mul (U * S) V]; simp only [Matrix.mul_assoc]
    rw [this, h0, Matrix.mul_one, hV]
  refine ⟨U * S * V, hH.eigenvalues, ?_, h1, ?_⟩
  · exact Matrix.isUnit_det_of_left_inverse h1
  · rw [← hVG, Matrix.conjTranspose_mul (U * S) V]; simp only [Matrix.mul_assoc]

end GlobalTheory.HSAmp
