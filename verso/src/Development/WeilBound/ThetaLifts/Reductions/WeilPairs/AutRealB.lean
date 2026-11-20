import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixed

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

/- English proof (translation)
Rewrite using `[GlobalTheory.RatAut.RealInt.dot_expM hH hQ, gaussV, omV_apply, omV_apply, jV_apply, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussV_eq {κ : Type} [Fintype κ] [DecidableEq κ] {H s g : Matrix κ κ ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef)
    (v : κ → ℂ) : gaussV H s g v =
      Complex.exp (-(Real.pi : ℂ) * (star v ⬝ᵥ GlobalTheory.RatAut.RealInt.expM H s g *ᵥ v)) := by
  rw [GlobalTheory.RatAut.RealInt.dot_expM hH hQ, gaussV, omV_apply, omV_apply, jV_apply, ← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Take `⟨-, h1, h2⟩` from `GlobalTheory.MatrixGaussian.integral_gaussian κ _ (GlobalTheory.RatAut.RealInt.expM_herm hQ hd)`. Establish `e : gaussV H s g = fun v => Complex.exp (-(Real.pi : ℂ) * (star v ⬝ᵥ GlobalTheory.RatAut.RealInt.expM H s g *ᵥ v))`. Use function extensionality and compare the values at `(gaussV_eq hH hQ)`. Use `⟨by rw [e]; exact h1, ?_, (H * s).det.re⁻¹, inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg det (GlobalTheory.RatAut.RealInt.expM_mul hH hs hg hc hi)`.

Simplify using `only [det_mul] at h3`. Establish `h4 : (-H).det * (-s).det = (H * s).det` using `by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]`. Introduce `h0`. Unfold `GlobalTheory.RealWeil.dP at h0`. Establish `h5 : (-H).det * (g - 1).det = 0` using `by rw [← h3, h0]; ring`.

Break down `mul_eq_zero.1 h5 with h6 | h6` into its components or cases. Conclude with `hQ.det_pos.ne' (by rw [← h4, h6, zero_mul])`. Conclude with `hd h6`. Rewrite using `[e, h2]`. Conclude with `GlobalTheory.RatAut.RealInt.gauss_det hH hs hQ hg hc hi hd`.
-/
theorem integral_gaussV_B {κ : Type} [Fintype κ] [DecidableEq κ] {H s g g' : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1)
    (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H) (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    Integrable (gaussV H s g) volume ∧ GlobalTheory.RealWeil.dP s g' ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV H s g v) * (g - 1).det = r * (-s).det * (g.det * GlobalTheory.RealWeil.dP s g') := by
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian κ _ (GlobalTheory.RatAut.RealInt.expM_herm hQ hd)
  have e : gaussV H s g = fun v => Complex.exp (-(Real.pi : ℂ) * (star v ⬝ᵥ GlobalTheory.RatAut.RealInt.expM H s g *ᵥ v)) :=
    funext (gaussV_eq hH hQ)
  refine ⟨by rw [e]; exact h1, ?_, (H * s).det.re⁻¹, inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1, ?_⟩
  · have h3 := congrArg det (GlobalTheory.RatAut.RealInt.expM_mul hH hs hg hc hi)
    simp only [det_mul] at h3
    have h4 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    intro h0
    unfold GlobalTheory.RealWeil.dP at h0
    have h5 : (-H).det * (g - 1).det = 0 := by rw [← h3, h0]; ring
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact hQ.det_pos.ne' (by rw [← h4, h6, zero_mul])
    · exact hd h6
  · rw [e, h2]
    exact GlobalTheory.RatAut.RealInt.gauss_det hH hs hQ hg hc hi hd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}

/- English proof (translation)
Establish `e1 : ∀ w, compAtF θ w (mtF σ JT h⁻¹) = b.map (tauB B w)` using `fun w => by`. Rewrite using `[show mtF σ JT h⁻¹ = b.map (incAF F E) from hb]`. Use extensionality with `i j`. Conclude with `PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _`. Establish `e2 : ∀ w, compAtF θ w (mtF σ JS g⁻¹⁻¹) = a.map (tauB B w)` using `fun w => by`.

Rewrite using `[inv_inv, show mtF σ JS g = a.map (incAF F E) from ha]`. Use extensionality with `i j`. Conclude with `PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _`. Establish `e3 : ∀ w, (b.map (tauB B w) ⊗ₖ (a.map (tauB B w))ᵀ) = (b ⊗ₖ aᵀ).map (tauB B w)` using `fun w => by`. Use extensionality with `⟨i, j⟩ ⟨k, l⟩`.

Simplify using `only [Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.transpose_apply, map_mul]`. Rewrite using `[mMF_apply]`. Simplify using `only [e1, e2]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.RatAut.RealInt.det_blk]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[e3]`. Conclude with `(RingHom.map_det _ _).symm`. Rewrite using `[GlobalTheory.RatAut.RealInt.det_blk_sub_one]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[e3, RingHom.map_det, map_sub, map_one]`. Both sides reduce to the same expression.
-/
theorem det_mMF_B (C : Ctx σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (mMF σ JS JT θ (g⁻¹, h⁻¹)).det = ∏ v, tauB B v (b ⊗ₖ aᵀ).det ∧
      (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det = ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det := by
  have e1 : ∀ w, compAtF θ w (mtF σ JT h⁻¹) = b.map (tauB B w) := fun w => by
    rw [show mtF σ JT h⁻¹ = b.map (incAF F E) from hb]
    ext i j
    exact PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _
  have e2 : ∀ w, compAtF θ w (mtF σ JS g⁻¹⁻¹) = a.map (tauB B w) := fun w => by
    rw [inv_inv, show mtF σ JS g = a.map (incAF F E) from ha]
    ext i j
    exact PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _
  have e3 : ∀ w, (b.map (tauB B w) ⊗ₖ (a.map (tauB B w))ᵀ) = (b ⊗ₖ aᵀ).map (tauB B w) := fun w => by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.transpose_apply, map_mul]
  rw [mMF_apply]
  simp only [e1, e2]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.RatAut.RealInt.det_blk]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3]
    exact (RingHom.map_det _ _).symm
  · rw [GlobalTheory.RatAut.RealInt.det_blk_sub_one]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3, RingHom.map_det, map_sub, map_one]
    rfl

end PositivityTheory.ThKW

end
