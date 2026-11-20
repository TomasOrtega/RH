import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

/- English proof (translation)
Use `set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef`. Use `set d : n → ℝ := hH.eigenvalues with hddef`. Establish `hUU : star U * U = 1` using `Unitary.coe_star_mul_self _`. Establish `hUU' : U * star U = 1` using `Unitary.coe_mul_star_self _`. Establish `hspec : H = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U`.

Use `hH.spectral_theorem` as an intermediate fact. Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `this`. Establish `hd : ∀ i, d i ≠ 0`. Introduce `i hi`.

Establish `h0` using `hdet.ne_zero`. Rewrite `h0` using `[hH.det_eq_prod_eigenvalues]`. Conclude with `h0 (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← hddef, hi]))`. Establish `hinv : H⁻¹ = U * diagonal (fun i => (((d i)⁻¹ : ℝ) : ℂ)) * star U`. Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations.

Rewrite using `[hspec]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]`. Establish `: (fun i => ((d i : ℝ) : ℂ) * (((d i)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `i`.

Rewrite using `[← Complex.ofReal_mul, mul_inv_cancel₀ (hd i), Complex.ofReal_one]`. Rewrite using `[this, diagonal_one, Matrix.one_mul, hUU']`. Use `⟨U * diagonal (fun i => ((|d i| : ℝ) : ℂ)) * star U, ?_, ?_⟩` and prove the remaining obligations. Establish `hD : (diagonal (fun i => ((|d i| : ℝ) : ℂ))).PosDef` using `Matrix.posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (abs_pos.mpr (hd i))`. Establish `hinj : Function.Injective U.vecMul`.

Introduce `x y hxy`. Use `congrArg (fun z => z ᵥ* star U) hxy` as an intermediate fact. Simplify `this` using `only [vecMul_vecMul, hUU', vecMul_one]`. Simplify `hD.mul_mul_conjTranspose_same hinj` using `only [star_eq_conjTranspose]`. Rewrite using `[hinv] conv_rhs => rw [hspec]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_posDef_mul_inv_mul_eq {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    ∃ P : Matrix n n ℂ, P.PosDef ∧ P * H⁻¹ * P = H := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set d : n → ℝ := hH.eigenvalues with hddef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    have h0 := hdet.ne_zero
    rw [hH.det_eq_prod_eigenvalues] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← hddef, hi]))
  have hinv : H⁻¹ = U * diagonal (fun i => (((d i)⁻¹ : ℝ) : ℂ)) * star U := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    have : (fun i => ((d i : ℝ) : ℂ) * (((d i)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hd i), Complex.ofReal_one]
    rw [this, diagonal_one, Matrix.one_mul, hUU']
  refine ⟨U * diagonal (fun i => ((|d i| : ℝ) : ℂ)) * star U, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|d i| : ℝ) : ℂ))).PosDef :=
      Matrix.posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (abs_pos.mpr (hd i))
    have hinj : Function.Injective U.vecMul := by
      intro x y hxy
      have := congrArg (fun z => z ᵥ* star U) hxy
      simpa only [vecMul_vecMul, hUU', vecMul_one] using this
    simpa only [star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same hinj
  · rw [hinv]
    conv_rhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
      Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc |d i| * (d i)⁻¹ * |d i| = |d i| * |d i| * (d i)⁻¹ := by ring
      _ = d i * d i * (d i)⁻¹ := by rw [abs_mul_abs_self]
      _ = d i := mul_inv_cancel_right₀ (hd i) _

section Spaces

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `choose P hP hPH using fun w => exists_posDef_mul_inv_mul_eq (h₁ w).1 (h₁ w).2`. Conclude with `⟨⟨P, hP, hPH⟩⟩`.
-/
theorem MajorantExists.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : GramAtData.Statement h v) : MajorantExists.Statement h v := by
  choose P hP hPH using fun w => exists_posDef_mul_inv_mul_eq (h₁ w).1 (h₁ w).2
  exact ⟨⟨P, hP, hPH⟩⟩

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
