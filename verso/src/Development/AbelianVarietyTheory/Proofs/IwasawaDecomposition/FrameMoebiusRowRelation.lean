import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

namespace GlobalTheory.ShFam

/- English proof (translation)
Introduce `E _ _ _ r X j hj hp x hx ψ`. Use `set C := frameCo X hj x ψ with hC`. Establish `hdet : IsUnit C.det`. Rewrite using `[hC, frameCo, det_reindex_self, det_mul]`. Conclude with `(isUnit_nonsing_inv_det _ (det_x0F X ψ).isUnit).mul (hx ψ).1.isUnit`.

Establish `hCC : C⁻¹ * C = 1` using `nonsing_inv_mul _ hdet`. Establish `hD` using `frameCo_isUnit₂₂ X hj hp hx ψ`. Rewrite `hD` using `[← hC]`. Use `⟨C⁻¹.submatrix Sum.inl id, ?_, ⟨C.submatrix id Sum.inl, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e1 : C.submatrix id Sum.inr = fromRows (moeb C 0) (1 : Matrix (Fin (r - j)) (Fin (r - j)) ℂ) * C.toBlocks₂₂`.

Rewrite using `[moeb_zero, fromRows_mul, Matrix.one_mul, Matrix.mul_assoc, nonsing_inv_mul _ hD, Matrix.mul_one]`. Use extensionality with `m k`. Apply the tactic sequence `rcases m with m | m <;> rfl`. Establish `e2 : C⁻¹.submatrix Sum.inl id * (fromRows (moeb C 0) (1 : Matrix (Fin (r - j)) (Fin (r - j)) ℂ) * C.toBlocks₂₂) = 0`. Rewrite using `[← e1]`.

Use extensionality with `i k`. Use `congrFun (congrFun hCC (Sum.inl i)) (Sum.inr k)` as an intermediate fact. Simplify `this` using `[mul_apply]`. Use `congrArg (· * C.toBlocks₂₂⁻¹) e2` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc, mul_nonsing_inv _ hD]`.

Use extensionality with `i i'`. Use `congrFun (congrFun hCC (Sum.inl i)) (Sum.inl i')` as an intermediate fact. Simplify `this` using `[mul_apply, one_apply]`. Introduce `v i hi`. Establish `hk : (idx hj).symm (Sum.inl i) = ⟨X.p0 + i, hi⟩` using `Fin.ext (by rw [idx_symm_inl]; exact congrArg (· + (i : ℕ)) hp.symm)`.

Establish `hM : (mat x ψ)⁻¹ = ((mat (x0F X) ψ)⁻¹ * mat x ψ)⁻¹ * (mat (x0F X) ψ)⁻¹`. Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_x0F X ψ).isUnit, Matrix.mul_assoc, mul_nonsing_inv _ (det_x0F X ψ).isUnit, Matrix.mul_one]`. Rewrite using `[hM, ← mulVec_mulVec, ← hk, hC, frameCo, inv_reindex]`. Simplify using `only [mulVec, dotProduct, reindex_apply, submatrix_apply, id]`. Conclude with `(Equiv.sum_comp (idx hj).symm _).symm`.
-/
theorem frameCo_inv_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (j : ℕ) (hj : j ≤ r), X.p0 = r - j → ∀ (x : Frame X.Ψ r), x ∈ X.dom → ∀ ψ : X.Ψ, ∃ R : Matrix (Fin j) (Fin j ⊕ Fin (r - j)) ℂ, R * Matrix.fromRows (moeb (frameCo X hj x ψ) 0) (1 : Matrix (Fin (r - j)) (Fin (r - j)) ℂ) = 0 ∧ (∃ Rr : Matrix (Fin j ⊕ Fin (r - j)) (Fin j) ℂ, R * Rr = 1) ∧ ∀ (v : Fin r → ℂ) (i : Fin j) (hi : X.p0 + (i : ℕ) < r), ((mat x ψ)⁻¹.mulVec v) ⟨X.p0 + i, hi⟩ = (R.mulVec fun m => ((mat (x0F X) ψ)⁻¹.mulVec v) ((idx hj).symm m)) i := by
  intro E _ _ _ r X j hj hp x hx ψ
  set C := frameCo X hj x ψ with hC
  have hdet : IsUnit C.det := by
    rw [hC, frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ (det_x0F X ψ).isUnit).mul (hx ψ).1.isUnit
  have hCC : C⁻¹ * C = 1 := nonsing_inv_mul _ hdet
  have hD := frameCo_isUnit₂₂ X hj hp hx ψ
  rw [← hC] at hD
  refine ⟨C⁻¹.submatrix Sum.inl id, ?_, ⟨C.submatrix id Sum.inl, ?_⟩, ?_⟩
  · have e1 : C.submatrix id Sum.inr = fromRows (moeb C 0) (1 : Matrix (Fin (r - j)) (Fin (r - j)) ℂ) * C.toBlocks₂₂ := by
      rw [moeb_zero, fromRows_mul, Matrix.one_mul, Matrix.mul_assoc, nonsing_inv_mul _ hD, Matrix.mul_one]
      ext m k
      rcases m with m | m <;> rfl
    have e2 : C⁻¹.submatrix Sum.inl id * (fromRows (moeb C 0) (1 : Matrix (Fin (r - j)) (Fin (r - j)) ℂ) * C.toBlocks₂₂) = 0 := by
      rw [← e1]
      ext i k
      have := congrFun (congrFun hCC (Sum.inl i)) (Sum.inr k)
      simpa [mul_apply] using this
    have := congrArg (· * C.toBlocks₂₂⁻¹) e2
    simpa [Matrix.mul_assoc, mul_nonsing_inv _ hD] using this
  · ext i i'
    have := congrFun (congrFun hCC (Sum.inl i)) (Sum.inl i')
    simpa [mul_apply, one_apply] using this
  · intro v i hi
    have hk : (idx hj).symm (Sum.inl i) = ⟨X.p0 + i, hi⟩ := Fin.ext (by rw [idx_symm_inl]; exact congrArg (· + (i : ℕ)) hp.symm)
    have hM : (mat x ψ)⁻¹ = ((mat (x0F X) ψ)⁻¹ * mat x ψ)⁻¹ * (mat (x0F X) ψ)⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_x0F X ψ).isUnit, Matrix.mul_assoc,
        mul_nonsing_inv _ (det_x0F X ψ).isUnit, Matrix.mul_one]
    rw [hM, ← mulVec_mulVec, ← hk, hC, frameCo, inv_reindex]
    simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, id]
    exact (Equiv.sum_comp (idx hj).symm _).symm

end GlobalTheory.ShFam
