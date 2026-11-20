import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapMoebiusDenomUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCover

set_option autoImplicit false

noncomputable section

open Matrix Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

namespace GlobalTheory.TorsionForm.FrameSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}

def EntSmooth {ι κ : Type} (f : E → Matrix ι κ ℂ) (B : Set E) : Prop :=
  ∀ i j, ContDiffOn ℝ ∞ (fun b => f b i j) B

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)` and prove the remaining obligations.
-/
theorem entSmooth_det {m : ℕ} {f : E → Matrix (Fin m) (Fin m) ℂ} (hf : EntSmooth f B) :
    ContDiffOn ℝ ∞ (fun b => (f b).det) B := by
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

/- English proof (translation)
Introduce `i k`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `using contDiffOn_const`. Simplify `hf i k` using `[Matrix.updateRow_ne h]`.
-/
theorem entSmooth_updateRow {m : ℕ} {f : E → Matrix (Fin m) (Fin m) ℂ} (hf : EntSmooth f B)
    (j : Fin m) (c : Fin m → ℂ) : EntSmooth (fun b => (f b).updateRow j c) B := by
  intro i k
  by_cases h : i = j
  · subst h; simpa using contDiffOn_const
  · simpa [Matrix.updateRow_ne h] using hf i k

/- English proof (translation)
Introduce `i j`. Establish `hd : ∀ b ∈ B, (f b).det ≠ 0` using `fun b hb => ((Matrix.isUnit_iff_isUnit_det _).1 (hu b hb)).ne_zero`. Establish `e : (fun b => (f b)⁻¹ i j) = fun b => ((f b).det)⁻¹ * (f b).adjugate i j`. Use function extensionality and compare the values at `b`. Simplify using `[Matrix.inv_def, Ring.inverse_eq_inv']`.

Rewrite using `[e]`. Use `((entSmooth_det hf).inv hd).mul ?_` and prove the remaining obligations. Simplify using `only [Matrix.adjugate_apply]`. Conclude with `entSmooth_det (entSmooth_updateRow hf _ _)`.
-/
theorem entSmooth_inv {m : ℕ} {f : E → Matrix (Fin m) (Fin m) ℂ} (hf : EntSmooth f B)
    (hu : ∀ b ∈ B, IsUnit (f b)) : EntSmooth (fun b => (f b)⁻¹) B := by
  intro i j
  have hd : ∀ b ∈ B, (f b).det ≠ 0 := fun b hb =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (hu b hb)).ne_zero
  have e : (fun b => (f b)⁻¹ i j) = fun b => ((f b).det)⁻¹ * (f b).adjugate i j := by
    funext b; simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  refine ((entSmooth_det hf).inv hd).mul ?_
  simp only [Matrix.adjugate_apply]
  exact entSmooth_det (entSmooth_updateRow hf _ _)

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.conjTranspose_apply]`. Conclude with `Complex.conjCLE.contDiff.comp_contDiffOn (hf j i)`.
-/
theorem entSmooth_conjTranspose {m : ℕ} {f : E → Matrix (Fin m) (Fin m) ℂ} (hf : EntSmooth f B) :
    EntSmooth (fun b => (f b)ᴴ) B := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hf j i)

/- English proof (translation)
Introduce `i j`. Simplify using `only [fibMat, Matrix.reindex_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases (finSumFinEquiv.symm i) with a | a <;> rcases (finSumFinEquiv.symm j) with c | c <;>`. Simplify using `only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]`. Apply the tactic sequence `all_goals first | exact contDiffOn_const | exact hf a c`.
-/
theorem entSmooth_fibMat (n : ℕ) {g : ℕ} {f : E → Matrix (Fin g) (Fin g) ℂ} (hf : EntSmooth f B) :
    EntSmooth (fun b => fibMat n (f b)) B := by
  intro i j
  simp only [fibMat, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.symm i) with a | a <;> rcases (finSumFinEquiv.symm j) with c | c <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]
  all_goals first | exact contDiffOn_const | exact hf a c

/- English proof (translation)
Use `contDiffOn_pi.2 fun S => ?_` and prove the remaining obligations. Simplify using `only [wedge]`. Use `split_ifs`. Conclude with `contDiffOn_const.mul (contDiffOn_pi.1 hw _)`. Conclude with `contDiffOn_const`.
-/
theorem contDiffOn_wedge {m : ℕ} (k : Fin m) {w : E → Ext m} (hw : ContDiffOn ℝ ∞ w B) :
    ContDiffOn ℝ ∞ (fun b => wedge k (w b)) B := by
  refine contDiffOn_pi.2 fun S => ?_
  simp only [wedge]
  split_ifs
  · exact contDiffOn_const.mul (contDiffOn_pi.1 hw _)
  · exact contDiffOn_const

/- English proof (translation)
Unfold `genProd`. Proceed by induction on `(S.sort (· ≤ ·)) with`. Consider the case `nil => exact contDiffOn_const`. Consider the case `cons i l ih`. Simplify using `only [List.foldr_cons]`.

Conclude with `ContDiffOn.sum fun k _ => (hφ i k).smul (contDiffOn_wedge k ih)`.
-/
theorem contDiffOn_genProd {m : ℕ} {φ : E → Matrix (Fin m) (Fin m) ℂ} (hφ : EntSmooth φ B)
    (S : Finset (Fin m)) : ContDiffOn ℝ ∞ (fun b => genProd (φ b) S) B := by
  unfold genProd
  induction (S.sort (· ≤ ·)) with
  | nil => exact contDiffOn_const
  | cons i l ih =>
    simp only [List.foldr_cons]
    exact ContDiffOn.sum fun k _ => (hφ i k).smul (contDiffOn_wedge k ih)

/- English proof (translation)
Use extensionality with `w : 1`. Simplify using `[extMap_apply, ContinuousLinearMap.sum_apply]`.
-/
theorem extMap_eq_sum {m : ℕ} (φ : Matrix (Fin m) (Fin m) ℂ) :
    extMap φ = ∑ S, (ContinuousLinearMap.proj S : Ext m →L[ℂ] ℂ).smulRight (genProd φ S) := by
  ext w : 1
  simp [extMap_apply, ContinuousLinearMap.sum_apply]

/- English proof (translation)
Simplify using `only [extMap_eq_sum]`. Use `ContDiffOn.sum fun S _ => ?_` and prove the remaining obligations. Conclude with `((ContinuousLinearMap.smulRightL ℂ (Ext m) (Ext m) (ContinuousLinearMap.proj S)).restrictScalars ℝ).contDiff.comp_contDiffOn (contDiffOn_genProd hφ S)`.
-/
theorem contDiffOn_extMap {m : ℕ} {φ : E → Matrix (Fin m) (Fin m) ℂ} (hφ : EntSmooth φ B) :
    ContDiffOn ℝ ∞ (fun b => extMap (φ b)) B := by
  simp only [extMap_eq_sum]
  refine ContDiffOn.sum fun S _ => ?_
  exact ((ContinuousLinearMap.smulRightL ℂ (Ext m) (Ext m)
    (ContinuousLinearMap.proj S)).restrictScalars ℝ).contDiff.comp_contDiffOn (contDiffOn_genProd hφ S)

/- English proof (translation)
Introduce `i j` and use `((GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn hτ.1.uniqueDiffOn).restrict_scalars ℝ`.
-/
theorem entSmooth_of_isPeriodMap [FiniteDimensional ℂ E] {g : ℕ} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) : EntSmooth τ B := fun i j =>
  ((GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn
    hτ.1.uniqueDiffOn).restrict_scalars ℝ

/- English proof (translation)
Introduce `i j`. Simplify using `only [den, Matrix.add_apply, Matrix.mul_apply]`. Conclude with `(ContDiffOn.sum fun k _ => contDiffOn_const.mul (hτ k j)).add contDiffOn_const`.
-/
theorem entSmooth_den {g : ℕ} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : EntSmooth τ B) (γ : Sp g) :
    EntSmooth (fun b => den γ (τ b)) B := by
  intro i j
  simp only [den, Matrix.add_apply, Matrix.mul_apply]
  exact (ContDiffOn.sum fun k _ => contDiffOn_const.mul (hτ k j)).add contDiffOn_const

end GlobalTheory.TorsionForm.FrameSmooth

namespace GlobalTheory.TorsionForm.Gauge

open GlobalTheory.TorsionForm.FrameSmooth in

/- English proof (translation)
Introduce `E _ _ _ g n B τ γ hτ hγ`. Conclude with `contDiffOn_extMap (entSmooth_fibMat n (entSmooth_conjTranspose (entSmooth_inv (entSmooth_den (entSmooth_of_isPeriodMap hτ) γ) (GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap B τ γ hγ))))`.
-/
theorem contDiffOn_frameAt : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g : ℕ} (n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g),
    IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) →
    ContDiffOn ℝ ∞ (fun b => frameAt n τ γ b) B := by
  intro E _ _ _ g n B τ γ hτ hγ
  exact contDiffOn_extMap (entSmooth_fibMat n (entSmooth_conjTranspose (entSmooth_inv
    (entSmooth_den (entSmooth_of_isPeriodMap hτ) γ)
    (GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap B τ γ hγ))))

end GlobalTheory.TorsionForm.Gauge
