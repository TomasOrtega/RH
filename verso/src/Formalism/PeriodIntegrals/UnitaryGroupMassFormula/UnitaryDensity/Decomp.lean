import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.GramStep

open Matrix
open scoped ComplexOrder

namespace PI.UD

/- English proof (translation)
Use `⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2`. Rewrite using `[← star_eq_conjTranspose]`. Conclude with `Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2`.

Establish `h` using `hA.spectral_theorem`. Rewrite `h` using `[Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]`. Establish `e : (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ) = fun i => ((hA.eigenvalues i : ℝ) : ℂ)`. Use function extensionality and compare the values at `i`. Both sides reduce to the same expression.

Rewrite `h` using `[e]`. Conclude with `h`.
-/
lemma herm_decomp {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  · rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
    have e : (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ) =
        fun i => ((hA.eigenvalues i : ℝ) : ℂ) := by
      funext i; rfl
    rw [e] at h
    exact h

/- English proof (translation)
Establish `h` using `congrArg det hU`. Rewrite `h` using `[det_mul, det_one]`. Conclude with `left_ne_zero_of_mul_eq_one h`.
-/
lemma det_ne_zero_of_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) :
    Uᴴ.det ≠ 0 := by
  have h := congrArg det hU
  rw [det_mul, det_one] at h
  exact left_ne_zero_of_mul_eq_one h

/- English proof (translation)
Take `⟨V, h1, h2, hV⟩` from `herm_decomp hG.1`. Use `⟨fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ), V, ?_, h1, h2, ?_⟩` and prove the remaining obligations. Introduce `i`. Conclude with `Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hG.eigenvalues_pos i)).ne'`. Establish `hd : (diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ * diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)) = diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ))`.

Rewrite using `[diagonal_conjTranspose, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (hG.eigenvalues_pos i).le]`.

Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_diagonal_unitary_gram_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) :
    ∃ (s : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ), (∀ i, s i ≠ 0) ∧ Vᴴ * V = 1 ∧
      V * Vᴴ = 1 ∧ G = (diagonal s * Vᴴ)ᴴ * (diagonal s * Vᴴ) := by
  obtain ⟨V, h1, h2, hV⟩ := herm_decomp hG.1
  refine ⟨fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ), V, ?_, h1, h2, ?_⟩
  · intro i
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hG.eigenvalues_pos i)).ne'
  · have hd : (diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ *
        diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)) =
        diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ)) := by
      rw [diagonal_conjTranspose, diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hG.eigenvalues_pos i).le]
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc G = V * diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ)) * Vᴴ := hV
      _ = V * ((diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ *
          diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ))) * Vᴴ := by rw [hd]
      _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `n G hG`. Take `⟨s, V, hs, hV1, -, hGe⟩` from `exists_diagonal_unitary_gram_of_posDef hG`. Use `⟨diagonal s * Vᴴ, hGe.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul, det_diagonal]`. Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i) (det_ne_zero_of_unitary hV1)`.
-/
theorem gramStep : GramStep := by
  intro n G hG
  obtain ⟨s, V, hs, hV1, -, hGe⟩ := exists_diagonal_unitary_gram_of_posDef hG
  refine ⟨diagonal s * Vᴴ, hGe.symm, ?_⟩
  rw [det_mul, det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i)
    (det_ne_zero_of_unitary hV1)

/- English proof (translation)
Introduce `n g hg`. Establish `hinj : Function.Injective g.mulVec` using `mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg))`. Establish `hP : (gᴴ * g).PosDef` using `PosDef.conjTranspose_mul_self g hinj`. Take `⟨s, V, hs, hV1, hV2, hG⟩` from `exists_diagonal_unitary_gram_of_posDef hP`. Use `set C := diagonal s * Vᴴ with hC`.

Establish `hCdet : IsUnit C.det`. Use `isUnit_iff_ne_zero.2 ?_` and prove the remaining obligations. Rewrite using `[hC, det_mul, det_diagonal]`. Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i) (det_ne_zero_of_unitary hV1)`. Establish `hCH : IsUnit Cᴴ.det`.

Rewrite using `[det_conjTranspose]`. Conclude with `hCdet.star`. Use `⟨g * C⁻¹, Vᴴ, s, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, conjTranspose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = (Cᴴ)⁻¹ * (Cᴴ * C) * C⁻¹ := by rw [hG]`. Use `_ = ((Cᴴ)⁻¹ * Cᴴ) * (C * C⁻¹) := by simp only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [nonsing_inv_mul _ hCH, mul_nonsing_inv _ hCdet, Matrix.one_mul]`. Rewrite using `[conjTranspose_conjTranspose]`.

Conclude with `hV2`. Rewrite using `[Matrix.mul_assoc (g * C⁻¹) (diagonal s) Vᴴ, ← hC, nonsing_inv_mul_cancel_right C g hCdet]`.
-/
theorem svdStep : SVDStep := by
  intro n g hg
  have hinj : Function.Injective g.mulVec :=
    mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg))
  have hP : (gᴴ * g).PosDef := PosDef.conjTranspose_mul_self g hinj
  obtain ⟨s, V, hs, hV1, hV2, hG⟩ := exists_diagonal_unitary_gram_of_posDef hP
  set C := diagonal s * Vᴴ with hC
  have hCdet : IsUnit C.det := by
    refine isUnit_iff_ne_zero.2 ?_
    rw [hC, det_mul, det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i)
      (det_ne_zero_of_unitary hV1)
  have hCH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hCdet.star
  refine ⟨g * C⁻¹, Vᴴ, s, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc (Cᴴ)⁻¹ * gᴴ * (g * C⁻¹) = (Cᴴ)⁻¹ * (gᴴ * g) * C⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (Cᴴ)⁻¹ * (Cᴴ * C) * C⁻¹ := by rw [hG]
      _ = ((Cᴴ)⁻¹ * Cᴴ) * (C * C⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hCH, mul_nonsing_inv _ hCdet, Matrix.one_mul]
  · rw [conjTranspose_conjTranspose]
    exact hV2
  · rw [Matrix.mul_assoc (g * C⁻¹) (diagonal s) Vᴴ, ← hC, nonsing_inv_mul_cancel_right C g hCdet]

end PI.UD
