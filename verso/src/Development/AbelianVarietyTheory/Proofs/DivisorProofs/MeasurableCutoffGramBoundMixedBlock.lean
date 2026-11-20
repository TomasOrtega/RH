import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

/- English proof (translation)
Introduce `r p0`. Establish `hlow : Continuous (fun w : Low r → ℂ => lowMat w)`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [lowMat]`. Apply the tactic sequence `split_ifs <;> first | exact continuous_apply _ | exact continuous_const`.

Establish `hblk : Continuous (fun w : Low r → ℂ => blkW p0 w)`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Establish `hent : ∀ a b : Fin r, Continuous (fun w : Low r → ℂ => lowMat w a b)` using `fun a b => (continuous_apply b).comp ((continuous_apply a).comp hlow)`. Distinguish the cases in `h : p0 = 1`. Simplify using `only [blkW, h, if_true]`.

Conclude with `hent _ _`. Simplify using `only [blkW, h, if_false]`. Conclude with `hent _ _`. Establish `hcg : ∀ k, Continuous (fun w : Low r → ℂ => colGram (blkW p0 w) k)`. Introduce `k`.

Simplify using `only [colGram, lminor]`. Conclude with `(((hblk.matrix_conjTranspose.matrix_mul hblk).matrix_submatrix _ _).matrix_det).norm`. Establish `hg : Measurable (fun w : Low r → ℂ => gB p0 w)`. Establish `hz : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹` using `fun x => by`. Rewrite using `[zpow_neg]`.

Use `norm_cast`. Simplify using `only [gB, hz]`. Use `Finset.measurable_prod _ fun k _ => ?_` and prove the remaining obligations. Conclude with `((hcg k.castSucc).measurable.pow_const 2).inv`. Establish `hS : IsClosed {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}`.

Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_le (continuous_apply p).norm continuous_const`. Unfold `hB`. Conclude with `(ENNReal.measurable_ofReal.comp hg).indicator hS.measurableSet`.
-/
theorem measurable_hB : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  intro r p0
  have hlow : Continuous (fun w : Low r → ℂ => lowMat w) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [lowMat]
    split_ifs <;> first | exact continuous_apply _ | exact continuous_const
  have hblk : Continuous (fun w : Low r → ℂ => blkW p0 w) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hent : ∀ a b : Fin r, Continuous (fun w : Low r → ℂ => lowMat w a b) := fun a b =>
      (continuous_apply b).comp ((continuous_apply a).comp hlow)
    by_cases h : p0 = 1
    · simp only [blkW, h, if_true]
      exact hent _ _
    · simp only [blkW, h, if_false]
      exact hent _ _
  have hcg : ∀ k, Continuous (fun w : Low r → ℂ => colGram (blkW p0 w) k) := by
    intro k
    simp only [colGram, lminor]
    exact (((hblk.matrix_conjTranspose.matrix_mul hblk).matrix_submatrix _ _).matrix_det).norm
  have hg : Measurable (fun w : Low r → ℂ => gB p0 w) := by
    have hz : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by
      rw [zpow_neg]; norm_cast
    simp only [gB, hz]
    refine Finset.measurable_prod _ fun k _ => ?_
    exact ((hcg k.castSucc).measurable.pow_const 2).inv
  have hS : IsClosed {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply p).norm continuous_const
  unfold hB
  exact (ENNReal.measurable_ofReal.comp hg).indicator hS.measurableSet

end GlobalTheory.IntBall
