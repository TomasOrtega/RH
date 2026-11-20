import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLBasis

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R K _ _ _ _ hinj k n ν ι b μ hb g t hg ht`. Establish `hD : IsUnit (Matrix.diagonal t).det`. Rewrite using `[Matrix.det_diagonal]`. Conclude with `isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => ht a)`. Establish `hgD : IsUnit (g * Matrix.diagonal t).det`.

Rewrite using `[Matrix.det_mul]`. Conclude with `hg.mul hD`. Establish `hDinv : (Matrix.diagonal t)⁻¹ = Matrix.diagonal (fun a => (t a)⁻¹)`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.diagonal_mul_diagonal]`.

Use `Matrix.diagonal_one with a` and compare the differences between its conclusion and the goal. Conclude with `inv_mul_cancel₀ (ht a)`. Establish `hfam : (fun i => rowAct K (g * Matrix.diagonal t)⁻¹ (map (algebraMap R K) (b i))) = fun i => (∏ a, t a ^ μ i a)⁻¹ • rowAct K g⁻¹ (map (algebraMap R K) (b i))`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mul_inv_rev, ← h1 K k n g⁻¹ (Matrix.diagonal t)⁻¹, AlgHom.comp_apply, hDinv, h2 K k n _ (μ i) _ (ldlat_isWH_map _ (hb.2.2 i)), map_smul]`.

Use `congr 1`. Rewrite using `[← Finset.prod_inv_distrib]`. Simplify using `[inv_pow]`. Take `⟨hl, hs⟩` from `h3 R K hinj k n ν b μ hb (g * Matrix.diagonal t) hgD`. Rewrite `hl`, `hs` using `[hfam]`.

Conclude with `⟨hl, hs⟩`.
-/
theorem nablaLDiag_of (h1 : RowActMul) (h2 : RowActDiagWeight) (h3 : NablaLBasis) : NablaLDiag := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g t hg ht
  have hD : IsUnit (Matrix.diagonal t).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => ht a)
  have hgD : IsUnit (g * Matrix.diagonal t).det := by
    rw [Matrix.det_mul]
    exact hg.mul hD
  have hDinv : (Matrix.diagonal t)⁻¹ = Matrix.diagonal (fun a => (t a)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with a
    exact inv_mul_cancel₀ (ht a)
  have hfam : (fun i => rowAct K (g * Matrix.diagonal t)⁻¹ (map (algebraMap R K) (b i))) =
      fun i => (∏ a, t a ^ μ i a)⁻¹ • rowAct K g⁻¹ (map (algebraMap R K) (b i)) := by
    funext i
    rw [Matrix.mul_inv_rev, ← h1 K k n g⁻¹ (Matrix.diagonal t)⁻¹, AlgHom.comp_apply, hDinv,
      h2 K k n _ (μ i) _ (ldlat_isWH_map _ (hb.2.2 i)), map_smul]
    congr 1
    rw [← Finset.prod_inv_distrib]
    simp [inv_pow]
  obtain ⟨hl, hs⟩ := h3 R K hinj k n ν b μ hb (g * Matrix.diagonal t) hgD
  rw [hfam] at hl hs
  exact ⟨hl, hs⟩

end Formalism.GradedWeylDivisibility
