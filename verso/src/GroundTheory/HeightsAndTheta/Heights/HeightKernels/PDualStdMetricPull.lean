import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.SingleMemDualLatticeStandard
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOnPlane
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField Matrix

noncomputable section

namespace StandardDualMetricPullback

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

omit [DecidableEq T] in

/- English proof (translation)
Use `set W := dualRecover b hb (fun t => z ⟨(), t⟩)`. Establish `hMW : dualEmbMatrix b *ᵥ W = fun t => z ⟨(), t⟩` using `(LinearEquiv.ofBijective _ hb).apply_symm_apply _`. Establish `hA : ∀ p : (K →+* ℂ) × Fin i, ∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p = p.1 ((Pi.single j 1 : Fin i → K) p.2)`. Introduce `p`. Rewrite using `[← dualStdCoordMat_sum b j, Finset.sum_apply, map_sum]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `[dualEmbMatrix, Pi.smul_apply, zsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [linApply]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[← congrFun hMW t]`. Both sides reduce to the same expression. Use `_ = ∑ p, (∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p) * W p := by`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.

Use `_ = ∑ τ : K →+* ℂ, W (τ, j) := by`. Simplify using `only [hA, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j (fun j' _ hj' => by simp [Ne.symm hj']) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem linApply_eq (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) (j : Fin i) :
    linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ =
      ∑ τ : K →+* ℂ, dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) := by
  set W := dualRecover b hb (fun t => z ⟨(), t⟩)
  have hMW : dualEmbMatrix b *ᵥ W = fun t => z ⟨(), t⟩ :=
    (LinearEquiv.ofBijective _ hb).apply_symm_apply _
  have hA : ∀ p : (K →+* ℂ) × Fin i,
      ∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p = p.1 ((Pi.single j 1 : Fin i → K) p.2) := by
    intro p
    rw [← dualStdCoordMat_sum b j, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [dualEmbMatrix, Pi.smul_apply, zsmul_eq_mul]
  calc linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩
      = ∑ t, (dualStdCoordMat b () j t : ℂ) * ∑ p, dualEmbMatrix b t p * W p := by
        simp only [linApply]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← congrFun hMW t]
        rfl
    _ = ∑ p, (∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p) * W p := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ τ : K →+* ℂ, W (τ, j) := by
        simp only [hA, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Ne.symm hj']) (by simp)]
        simp

end StandardDualMetricPullback

open StandardDualMetricPullback in

/- English proof (translation)
Introduce `K _ _ i T _ _ b hb z hz`. Use `set W := dualRecover b hb (fun t => z ⟨(), t⟩)`. Take `⟨σ, hσ⟩` from `DualPtsOnPlane.proof K i _ T b hb z hz`. Establish `hy : ∀ j, linApply (ι₂` using `PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ = W (σ, j) := fun j => by`. Rewrite using `[linApply_eq b hb z j]`.

Conclude with `Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)`. Establish `hterm : ∀ τ, ((star fun j => W (τ, j)) ⬝ᵥ ((HermLattice.standard K i).metric τ *ᵥ fun j => W (τ, j))).re = ∑ j, ‖W (τ, j)‖ ^ 2`. Introduce `τ`. Simplify using `only [HermLattice.standard, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[RCLike.star_def, Complex.conj_mul']`. Use `norm_cast`. Use `show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = _`. Rewrite using `[show dualNormSq b hb (fun t => z ⟨(), t⟩) = ∑ τ, ∑ j, ‖W (τ, j)‖ ^ 2 from Finset.sum_congr rfl fun τ _ => hterm τ]`. Simplify using `only [fsMulti, HermLine.ofMetrics, fsMetric, Finset.univ_unique, Finset.prod_singleton, zpow_one, EuclideanSpace.norm_eq]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single σ (fun τ _ hτ => by simp [W, hσ τ hτ]) (by simp)]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [← hy j]`.
-/
theorem DualStdMetricPull.proof : DualStdMetricPull.Statement := by
  intro K _ _ i T _ _ b hb z hz
  set W := dualRecover b hb (fun t => z ⟨(), t⟩)
  obtain ⟨σ, hσ⟩ := DualPtsOnPlane.proof K i _ T b hb z hz
  have hy : ∀ j, linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ = W (σ, j) := fun j => by
    rw [linApply_eq b hb z j]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  have hterm : ∀ τ, ((star fun j => W (τ, j)) ⬝ᵥ
      ((HermLattice.standard K i).metric τ *ᵥ fun j => W (τ, j))).re = ∑ j, ‖W (τ, j)‖ ^ 2 := by
    intro τ
    simp only [HermLattice.standard, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
    norm_cast
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = _
  rw [show dualNormSq b hb (fun t => z ⟨(), t⟩) = ∑ τ, ∑ j, ‖W (τ, j)‖ ^ 2 from
    Finset.sum_congr rfl fun τ _ => hterm τ]
  simp only [fsMulti, HermLine.ofMetrics, fsMetric, Finset.univ_unique, Finset.prod_singleton, zpow_one,
    EuclideanSpace.norm_eq]
  congr 1
  rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [W, hσ τ hτ]) (by simp)]
  exact Finset.sum_congr rfl fun j _ => by rw [← hy j]

end

end GroundTheory.Heights₂.Heights
