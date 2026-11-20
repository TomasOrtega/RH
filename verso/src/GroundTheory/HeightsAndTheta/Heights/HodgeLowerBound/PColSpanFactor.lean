import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

/- English proof (translation)
Introduce `N r h A g _hA hg hspan`. Establish `hmem : ∀ b : Fin r, (fun p => firstCols g r h p b) ∈ Submodule.span ℂ (Set.range fun a : Fin r => fun p => firstCols A r h p a)` using `fun b => hspan (Submodule.subset_span ⟨b, rfl⟩)`. Use `choose c hc using fun b => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem b)`. Set `M : Matrix (Fin r) (Fin r) ℂ` to `fun a b => c b a`. Establish `hM : firstCols g r h = firstCols A r h * M`.

Use extensionality with `p b`. Rewrite using `[← congrFun (hc b) p]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Use `⟨M, hM, fun hdet => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Establish `hli : LinearIndependent ℂ (fun a : Fin r => fun p => firstCols g r h p a)` using `(Matrix.linearIndependent_cols_of_det_ne_zero hg).comp _ (Fin.castLE_injective h)`. Establish `hgx : firstCols g r h *ᵥ x = 0`. Rewrite using `[hM, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]`. Establish `hsum : ∑ a, x a • (fun p => firstCols g r h p a) = 0`.

Use extensionality with `p`. Simplify `congrFun hgx p` using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Conclude with `hx0 (funext fun a => Fintype.linearIndependent_iff.1 hli x hsum a)`.
-/
theorem ColSpanFactor.proof : ColSpanFactor.Statement := by
  intro N r h A g _hA hg hspan
  have hmem : ∀ b : Fin r, (fun p => firstCols g r h p b) ∈
      Submodule.span ℂ (Set.range fun a : Fin r => fun p => firstCols A r h p a) :=
    fun b => hspan (Submodule.subset_span ⟨b, rfl⟩)
  choose c hc using fun b => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem b)
  let M : Matrix (Fin r) (Fin r) ℂ := fun a b => c b a
  have hM : firstCols g r h = firstCols A r h * M := by
    ext p b
    rw [← congrFun (hc b) p]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨M, hM, fun hdet => ?_⟩
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hli : LinearIndependent ℂ (fun a : Fin r => fun p => firstCols g r h p a) :=
    (Matrix.linearIndependent_cols_of_det_ne_zero hg).comp _ (Fin.castLE_injective h)
  have hgx : firstCols g r h *ᵥ x = 0 := by
    rw [hM, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hsum : ∑ a, x a • (fun p => firstCols g r h p a) = 0 := by
    ext p
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using congrFun hgx p
  exact hx0 (funext fun a => Fintype.linearIndependent_iff.1 hli x hsum a)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
