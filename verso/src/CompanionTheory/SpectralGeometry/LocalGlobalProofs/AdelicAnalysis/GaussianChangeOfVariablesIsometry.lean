import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW.GaussOrth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

/- English proof (translation)
Establish `h : (gᵀ * M * g) *ᵥ x = gᵀ *ᵥ (M *ᵥ (g *ᵥ x))`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[h, Matrix.dotProduct_mulVec x gᵀ, Matrix.vecMul_transpose]`.
-/
theorem quad_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (g M : Matrix ι ι ℝ) (x : ι → ℝ) :
    (g *ᵥ x) ⬝ᵥ (M *ᵥ (g *ᵥ x)) = x ⬝ᵥ ((gᵀ * M * g) *ᵥ x) := by
  have h : (gᵀ * M * g) *ᵥ x = gᵀ *ᵥ (M *ᵥ (g *ᵥ x)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h, Matrix.dotProduct_mulVec x gᵀ, Matrix.vecMul_transpose]

/- English proof (translation)
Establish `h1` using `congrArg Matrix.det h`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Establish `h2 : g.det * g.det = 1`. Apply `mul_right_cancel₀ hM` to reduce the goal to its premises. Rewrite using `[one_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : |g.det| * |g.det| = 1` using `by rw [← abs_mul, h2, abs_one]`. Establish `h4 : 0 ≤ |g.det|` using `abs_nonneg _`. Use polynomial arithmetic with `[sq_nonneg (|g.det| - 1), sq_nonneg (|g.det| + 1)]`.
-/
theorem abs_det_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {g M : Matrix ι ι ℝ}
    (hM : M.det ≠ 0) (h : gᵀ * M * g = M) : |g.det| = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : g.det * g.det = 1 := by
    apply mul_right_cancel₀ hM
    rw [one_mul]
    calc g.det * g.det * M.det = g.det * M.det * g.det := by ring
      _ = M.det := h1
  have h3 : |g.det| * |g.det| = 1 := by rw [← abs_mul, h2, abs_one]
  have h4 : 0 ≤ |g.det| := abs_nonneg _
  nlinarith [sq_nonneg (|g.det| - 1), sq_nonneg (|g.det| + 1)]

/- English proof (translation)
Establish `hd : g.det ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, abs_zero]`. Conclude with `zero_ne_one h`. Use `⟨(Continuous.matrix_mulVec continuous_const continuous_id).measurable, ?_⟩` and prove the remaining obligations.

Use `Real.map_matrix_volume_pi_eq_smul_volume_pi hd` as an intermediate fact. Establish `e : (fun x : ι → ℝ => g *ᵥ x) = ⇑(Matrix.toLin' g)`. Use extensionality with `x i`. Simplify using `[Matrix.toLin'_apply]`. Rewrite using `[e, this, abs_inv, h]`.

Simplify using the standard rewrite rules.
-/
theorem measurePreserving_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {g : Matrix ι ι ℝ}
    (h : |g.det| = 1) : MeasurePreserving (fun x : ι → ℝ => g *ᵥ x) volume volume := by
  have hd : g.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h
    exact zero_ne_one h
  refine ⟨(Continuous.matrix_mulVec continuous_const continuous_id).measurable, ?_⟩
  have := Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  have e : (fun x : ι → ℝ => g *ᵥ x) = ⇑(Matrix.toLin' g) := by
    ext x i
    simp [Matrix.toLin'_apply]
  rw [e, this, abs_inv, h]
  simp

/- English proof (translation)
Establish `hu : ∀ w, IsUnit (g w).det` using `fun w => isUnit_iff_ne_zero.mpr (h w)`. Set `e : (W → ι → ℝ) ≃ᵐ (W → ι → ℝ)` to `{ toFun := fun x w => g w *ᵥ x w invFun := fun x w => (g w)⁻¹ *ᵥ x w left_inv := by`. Introduce `x`. Use function extensionality and compare the values at `w`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu w), Matrix.one_mulVec]`.

Use `right_inv := by`. Introduce `x`. Use function extensionality and compare the values at `w`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mulVec]`. Use `measurable_toFun := by`.

Use `Continuous.measurable (continuous_pi fun w => ?_)` and prove the remaining obligations. Conclude with `Continuous.matrix_mulVec continuous_const (continuous_apply w)`. Use `measurable_invFun := by`. Use `Continuous.measurable (continuous_pi fun w => ?_)` and prove the remaining obligations. Conclude with `Continuous.matrix_mulVec continuous_const (continuous_apply w) }`.

Conclude with `e.measurableEmbedding`.
-/
theorem measurableEmbedding_mulVec {W ι : Type} [Fintype W] [Fintype ι] [DecidableEq ι]
    {g : W → Matrix ι ι ℝ} (h : ∀ w, (g w).det ≠ 0) :
    MeasurableEmbedding (fun (x : W → ι → ℝ) (w : W) => g w *ᵥ x w) := by
  have hu : ∀ w, IsUnit (g w).det := fun w => isUnit_iff_ne_zero.mpr (h w)
  let e : (W → ι → ℝ) ≃ᵐ (W → ι → ℝ) :=
    { toFun := fun x w => g w *ᵥ x w
      invFun := fun x w => (g w)⁻¹ *ᵥ x w
      left_inv := by
        intro x
        funext w
        simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu w), Matrix.one_mulVec]
      right_inv := by
        intro x
        funext w
        simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mulVec]
      measurable_toFun := by
        refine Continuous.measurable (continuous_pi fun w => ?_)
        exact Continuous.matrix_mulVec continuous_const (continuous_apply w)
      measurable_invFun := by
        refine Continuous.measurable (continuous_pi fun w => ?_)
        exact Continuous.matrix_mulVec continuous_const (continuous_apply w) }
  exact e.measurableEmbedding

/- English proof (translation)
Establish `first : ∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ), gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x`. Introduce `τ x`. Unfold `gauss`. Use `congr 1`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[quad_mulVec, quad_mulVec, hg w]`. Use `⟨first, fun τ => ?_⟩` and prove the remaining obligations. Establish `hdet : ∀ w, (B.map (ρ w)).det ≠ 0`. Introduce `w`. Establish `e : (B.map (ρ w)).det = ρ w B.det` using `(RingHom.map_det (ρ w) B).symm`.

Rewrite using `[e]`. Conclude with `(map_ne_zero (ρ w)).mpr hB`. Establish `habs : ∀ w, |(gi w).det| = 1` using `fun w => abs_det_eq_one (hdet w) (hg w)`. Establish `hne : ∀ w, (gi w).det ≠ 0`. Introduce `w h0`.

Use `habs w` as an intermediate fact. Rewrite `this` using `[h0, abs_zero]`. Conclude with `zero_ne_one this`. Establish `hmp : MeasurePreserving (fun (x : InfinitePlace F → ι → ℝ) w => gi w *ᵥ x w) volume volume` using `volume_preserving_pi fun w => measurePreserving_mulVec (habs w)`. Establish `hint` using `hmp.integral_comp (measurableEmbedding_mulVec hne) (gauss B ρ P τ)`.

Unfold `cG`. Rewrite using `[← hint]`. Use `congr 1`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun x => (first τ x).symm)`.
-/
theorem gauss_orth {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (hB : B.det ≠ 0)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    (∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x) ∧
    ∀ τ : InfinitePlace F → ℂ, cG B ρ (fun w => (gi w)ᵀ * P w * gi w) τ = cG B ρ P τ := by
  have first : ∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x := by
    intro τ x
    unfold gauss
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [quad_mulVec, quad_mulVec, hg w]
  refine ⟨first, fun τ => ?_⟩
  have hdet : ∀ w, (B.map (ρ w)).det ≠ 0 := by
    intro w
    have e : (B.map (ρ w)).det = ρ w B.det := (RingHom.map_det (ρ w) B).symm
    rw [e]
    exact (map_ne_zero (ρ w)).mpr hB
  have habs : ∀ w, |(gi w).det| = 1 := fun w => abs_det_eq_one (hdet w) (hg w)
  have hne : ∀ w, (gi w).det ≠ 0 := by
    intro w h0
    have := habs w
    rw [h0, abs_zero] at this
    exact zero_ne_one this
  have hmp : MeasurePreserving (fun (x : InfinitePlace F → ι → ℝ) w => gi w *ᵥ x w)
      volume volume :=
    volume_preserving_pi fun w => measurePreserving_mulVec (habs w)
  have hint := hmp.integral_comp (measurableEmbedding_mulVec hne) (gauss B ρ P τ)
  unfold cG
  rw [← hint]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (first τ x).symm)

end GlobalTheory.CompanionTheory.SW.ThW.GaussOrth

/- English proof (translation)
Introduce `_ _ _ _ _ _ B ρ P gi hB hg` and use `GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.gauss_orth B ρ P gi hB hg`.
-/
theorem GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (ρ : NumberField.InfinitePlace F → (F →+* ℝ)) (P : NumberField.InfinitePlace F → Matrix ι ι ℝ) (gi : NumberField.InfinitePlace F → Matrix ι ι ℝ), B.det ≠ 0 → (∀ w, (gi w).transpose * B.map (ρ w) * gi w = B.map (ρ w)) → (∀ (τ : NumberField.InfinitePlace F → ℂ) (x : NumberField.InfinitePlace F → ι → ℝ), GlobalTheory.CompanionTheory.SW.Core.gauss B ρ P τ (fun w => (gi w).mulVec (x w)) = GlobalTheory.CompanionTheory.SW.Core.gauss B ρ (fun w => (gi w).transpose * P w * gi w) τ x) ∧ ∀ τ : NumberField.InfinitePlace F → ℂ, GlobalTheory.CompanionTheory.SW.Core.cG B ρ (fun w => (gi w).transpose * P w * gi w) τ = GlobalTheory.CompanionTheory.SW.Core.cG B ρ P τ :=
  fun _ _ _ _ _ _ B ρ P gi hB hg => GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.gauss_orth B ρ P gi hB hg
