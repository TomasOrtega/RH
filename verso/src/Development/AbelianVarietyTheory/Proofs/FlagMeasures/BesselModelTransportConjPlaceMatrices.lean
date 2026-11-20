import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTransportIsometryFrameAdapted
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp.Transp

/- English proof (translation)
Establish `hu : IsUnit (X.B.I.P (vOf X (tauOf D w))).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _)`. Establish `h1 : (X.B.I.P (vOf X (tauOf D w)))⁻¹ * X.B.I.P (vOf X (tauOf D w)) = 1` using `Matrix.nonsing_inv_mul _ hu`. Take `⟨hQ, -, -, -⟩` from `C.isT (tauOf D w)`. Rewrite using `[A0, ← submatrix_mul _ _ id (ci X) id (ci X).bijective]`. Establish `: C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹ * (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)) = 1`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc _ (X.B.I.P _), h1, Matrix.one_mul, hQ]`. Rewrite using `[this, submatrix_id_id]`.
-/
theorem besselModelTransportMatrix_mul_right {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    A0 X C w * (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)).submatrix (ci X) id = 1 := by
  have hu : IsUnit (X.B.I.P (vOf X (tauOf D w))).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _)
  have h1 : (X.B.I.P (vOf X (tauOf D w)))⁻¹ * X.B.I.P (vOf X (tauOf D w)) = 1 := Matrix.nonsing_inv_mul _ hu
  obtain ⟨hQ, -, -, -⟩ := C.isT (tauOf D w)
  rw [A0, ← submatrix_mul _ _ id (ci X) id (ci X).bijective]
  have : C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹ * (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (X.B.I.P _), h1, Matrix.one_mul, hQ]
  rw [this, submatrix_id_id]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (besselModelTransportMatrix_mul_right X C w)`.
-/
theorem besselModelTransportMatrix_inv_eq_frame {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    (A0 X C w)⁻¹ = (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)).submatrix (ci X) id :=
  Matrix.inv_eq_right_inv (besselModelTransportMatrix_mul_right X C w)

/- English proof (translation)
Establish `hu : IsUnit (X.B.I.P (vOf X (tauOf D w))).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _)`. Establish `h1 : (X.B.I.P (vOf X (tauOf D w)))⁻¹ * X.B.I.P (vOf X (tauOf D w)) = 1` using `Matrix.nonsing_inv_mul _ hu`. Rewrite using `[besselModelTransportMatrix_inv_eq_frame, A0, ← submatrix_mul _ _ id (ci X) (ci X) (ci X).bijective, ← submatrix_mul _ _ id (ci X) id (ci X).bijective, submatrix_id_id, Formalism.L2.SG.RealObj.trG]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc _ (X.B.I.P _) (uMat _ * _), h1, Matrix.one_mul, ← Matrix.mul_assoc (X.B.I.P _)⁻¹ (X.B.I.P _) (C.Q _), h1, Matrix.one_mul]`.
-/
theorem besselModelTransportMatrix_conj_realPoint {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (w : InfinitePlace D.host.E) :
    A0 X C w * ((X.B.I.P (vOf X (tauOf D w)) * uMat (s (vOf X (tauOf D w))) * (X.B.I.P (vOf X (tauOf D w)))⁻¹).submatrix (ci X) (ci X))
      * (A0 X C w)⁻¹ = Formalism.L2.SG.RealObj.trG (C.Q (tauOf D w)) (C.Qi (tauOf D w)) (s (vOf X (tauOf D w))) := by
  have hu : IsUnit (X.B.I.P (vOf X (tauOf D w))).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _)
  have h1 : (X.B.I.P (vOf X (tauOf D w)))⁻¹ * X.B.I.P (vOf X (tauOf D w)) = 1 := Matrix.nonsing_inv_mul _ hu
  rw [besselModelTransportMatrix_inv_eq_frame, A0, ← submatrix_mul _ _ id (ci X) (ci X) (ci X).bijective,
    ← submatrix_mul _ _ id (ci X) id (ci X).bijective, submatrix_id_id, Formalism.L2.SG.RealObj.trG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ (X.B.I.P _) (uMat _ * _), h1, Matrix.one_mul,
    ← Matrix.mul_assoc (X.B.I.P _)⁻¹ (X.B.I.P _) (C.Q _), h1, Matrix.one_mul]

/- English proof (translation)
Introduce `D X θ C s γ hγ w`. Establish `key` using `besselModelTransportMatrix_conj_realPoint X C s w`. Rewrite `key` using `[← hγ]`. Unfold `Ac Gm cjw trX`. Use `split_ifs with hd`.

Rewrite using `[show w.embedding = embS D (tauOf D w) from hd, key]`. Both sides reduce to the same expression. Rewrite using `[ModelIso.embedding_of_not_direct w hd]`. Establish `hg : γ.map (ComplexEmbedding.conjugate (embS D (tauOf D w))) = (γ.map (embS D (tauOf D w))).map (starRingEnd ℂ)`. Use extensionality with `i j`.

Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Establish `hinv : ((A0 X C w).map star)⁻¹ = ((A0 X C w)⁻¹).map (starRingEnd ℂ)`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← Matrix.map_mul, besselModelTransportMatrix_inv_eq_frame, besselModelTransportMatrix_mul_right, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[hg, hinv, show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← Matrix.map_mul, ← Matrix.map_mul, key]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem transp : ∀ {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ τ, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (s (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X)) → ∀ w : InfinitePlace D.host.E, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w) := by
  intro D X θ C s γ hγ w
  have key := besselModelTransportMatrix_conj_realPoint X C s w
  rw [← hγ] at key
  unfold Ac Gm cjw trX
  split_ifs with hd
  · rw [show w.embedding = embS D (tauOf D w) from hd, key]
    rfl
  · rw [ModelIso.embedding_of_not_direct w hd]
    have hg : γ.map (ComplexEmbedding.conjugate (embS D (tauOf D w))) = (γ.map (embS D (tauOf D w))).map (starRingEnd ℂ) := by
      ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
    have hinv : ((A0 X C w).map star)⁻¹ = ((A0 X C w)⁻¹).map (starRingEnd ℂ) := by
      apply Matrix.inv_eq_right_inv
      rw [show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← Matrix.map_mul, besselModelTransportMatrix_inv_eq_frame, besselModelTransportMatrix_mul_right,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hg, hinv, show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← Matrix.map_mul, ← Matrix.map_mul, key]
    ext i j
    simp

end GlobalTheory.CovDomGrp.Transp
