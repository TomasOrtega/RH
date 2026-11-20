import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

/- English proof (translation)
Use `haveI := (hU n μ).1`. Establish `hm : MeasurePreserving (fun y : G n => y * h) μ μ` using `measurePreserving_mul_right μ h`. Establish `he : MeasurableEmbedding (fun y : G n => y * h)` using `(Homeomorph.mulRight h).measurableEmbedding`. Establish `h1 : Mol μ φ (⇑(rR μ V h x)) z = ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x (u * h) ∂μ`. Unfold `Mol`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [rR_coe μ hU h x] with u hu`. Rewrite using `[hu]`. Rewrite using `[h1]`. Unfold `Mol`.

Rewrite using `[← hm.integral_comp he (fun u : G n => φ (z * h.val * (u⁻¹ : G n).val) • x u)]`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `: z * h.val * ((u * h)⁻¹ : G n).val = z * (u⁻¹ : G n).val`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Simplify using `only [this]`.
-/
theorem Mol_rR_eq (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (hU : Unimod) (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n) :
    Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have he : MeasurableEmbedding (fun y : G n => y * h) := (Homeomorph.mulRight h).measurableEmbedding
  have h1 : Mol μ φ (⇑(rR μ V h x)) z = ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x (u * h) ∂μ := by
    unfold Mol
    refine integral_congr_ae ?_
    filter_upwards [rR_coe μ hU h x] with u hu
    rw [hu]
  rw [h1]
  unfold Mol
  rw [← hm.integral_comp he (fun u : G n => φ (z * h.val * (u⁻¹ : G n).val) • x u)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have : z * h.val * ((u * h)⁻¹ : G n).val = z * (u⁻¹ : G n).val := by
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp only [this]

end GlobalTheory.CompanionTheory.PresSobA
