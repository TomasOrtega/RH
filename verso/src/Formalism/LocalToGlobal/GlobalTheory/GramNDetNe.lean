import Formalism.LocalToGlobal.GlobalTheory.SigDEqStar
import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoordH

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `(Matrix.inv_eq_right_inv ?_).symm` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
theorem map_inv_mat {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.map_one _ (map_zero f) (map_one f)]

variable {D : D7}

/- English proof (translation)
Unfold `gramN`. Rewrite using `[Matrix.det_reindex_self]`. Conclude with `Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc.gram_det_ne (D.sp.X 0) (D.sp.X 0).frame`.
-/
theorem gramN_det_ne : (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  unfold gramN
  rw [Matrix.det_reindex_self]
  exact Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc.gram_det_ne (D.sp.X 0) (D.sp.X 0).frame

variable {u : D.what₂.Word} (B : ColBase D u)

/- English proof (translation)
Introduce `h0`. Establish `hY` using `congrArg Matrix.det (gram_Y B (InfinitePlace.mk D.what₂.embLL) c τ)`. Establish `e1 : (Ymat B (InfinitePlace.mk D.what₂.embLL) c τ).det = 0`. Rewrite using `[Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]`. Rewrite `hY` using `[Matrix.det_mul, e1, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Conclude with `gramN_det_ne (((InfinitePlace.mk D.what₂.embLL).embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))`.
-/
theorem Mb_det_ne (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Mb B c τ).det ≠ 0 := by
  intro h0
  have hY := congrArg Matrix.det (gram_Y B (InfinitePlace.mk D.what₂.embLL) c τ)
  have e1 : (Ymat B (InfinitePlace.mk D.what₂.embLL) c τ).det = 0 := by
    rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  rw [Matrix.det_mul, e1, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hY
  exact gramN_det_ne (((InfinitePlace.mk D.what₂.embLL).embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))

def gC (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : GL (Fin (D.R.N 0)) D.what₂.LL :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Mb B c τ * ((gramN D 0 (Nat.zero_le _)).map (B.rho τ))⁻¹) (by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero (Mb_det_ne B c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gC_coe (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) =
      Mb B c τ * ((gramN D 0 (Nat.zero_le _)).map (B.rho τ))⁻¹ := rfl

def Zc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Ymat B v c τ * ((gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)))⁻¹

/- English proof (translation)
Establish `hd : ((gramN D 0 (Nat.zero_le _)).map (B.rho τ)).det ≠ 0`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero _).2 gramN_det_ne`. Rewrite using `[gC_coe, Matrix.map_mul, map_inv_mat _ _ hd, Matrix.map_map, Zc, Ymat, Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem R_gC (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹ *
      ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL).map v.embedding =
      Zc B v c τ := by
  have hd : ((gramN D 0 (Nat.zero_le _)).map (B.rho τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 gramN_det_ne
  rw [gC_coe, Matrix.map_mul, map_inv_mat _ _ hd, Matrix.map_map, Zc, Ymat, Matrix.mul_assoc]
  rfl

/- English proof (translation)
Introduce `h0`. Establish `hY` using `congrArg Matrix.det (gram_Y B v c τ)`. Rewrite `hY` using `[Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `gramN_det_ne ((v.embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))`.
-/
theorem Y_det_ne (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Ymat B v c τ).det ≠ 0 := by
  intro h0
  have hY := congrArg Matrix.det (gram_Y B v c τ)
  rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hY
  exact gramN_det_ne ((v.embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))

/- English proof (translation)
Rewrite using `[Zc, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `mul_ne_zero (Y_det_ne B v c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne))`.
-/
theorem Zc_det_ne (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Zc B v c τ).det ≠ 0 := by
  rw [Zc, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact mul_ne_zero (Y_det_ne B v c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne))

/- English proof (translation)
Use `set P := (gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)) with hPdef`. Use `set Y := Ymat B v c τ`. Use `set G' := (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ)`. Establish `hYP : Yᴴ * Y = P` using `gram_Y B v c τ`. Establish `hGs : ∀ i j, star (gramN D 0 (Nat.zero_le _) j i) = gramN D 0 (Nat.zero_le _) i j` using `fun i j => by`.

Use `congrFun (congrFun (gramN_herm (D := D)) i) j` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_apply]`. Then use the resulting hypothesis. Establish `hP : Pᴴ = P`. Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, hPdef, Matrix.map_apply, Matrix.map_apply, ← hGs i j, RingHom.comp_apply, RingHom.comp_apply]`.

Establish `h1` using `host_emb_star D (v.embedding.comp (B.rho τ)) (gramN D 0 (Nat.zero_le _) j i)`. Simplify using `only [RingHom.comp_apply] at h1`. Rewrite using `[h1]`. Both sides reduce to the same expression. Establish `hG' : G'ᵀ = P`.

Use extensionality with `i j`. Simplify using `only [G', hPdef, Matrix.transpose_apply, Matrix.map_apply, RingHom.comp_apply]`. Rewrite using `[hB, rhoC_conj, ← host_emb_star D (embS D v.embedding τ), hGs j i]`. Establish `hdY : IsUnit Y.det` using `isUnit_iff_ne_zero.2 (Y_det_ne B v c τ)`. Establish `hdYh : IsUnit Yᴴ.det` using `by rw [Matrix.det_conjTranspose]; exact hdY.star`.

Establish `hdP : IsUnit P.det` using `by rw [← hYP, Matrix.det_mul]; exact hdYh.mul hdY`. Establish `key : Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ = 1`. Rewrite using `[hG', Zc, ← hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP]`. Combine the equalities or inequalities in the displayed calculation. Establish `ht : ((Zc B v c τ)ᵀ)ᴴ * G' * (Zc B v c τ)ᵀ = (Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ)ᵀ`.

Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[ht, key, Matrix.transpose_one]`.
-/
theorem Zc_on (hB : B.rho = rhoC D) (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((Zc B v c τ)ᵀ)ᴴ * (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ) * (Zc B v c τ)ᵀ = 1 := by
  set P := (gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)) with hPdef
  set Y := Ymat B v c τ
  set G' := (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ)
  have hYP : Yᴴ * Y = P := gram_Y B v c τ
  have hGs : ∀ i j, star (gramN D 0 (Nat.zero_le _) j i) = gramN D 0 (Nat.zero_le _) i j := fun i j => by
    have := congrFun (congrFun (gramN_herm (D := D)) i) j
    rwa [Matrix.conjTranspose_apply] at this
  have hP : Pᴴ = P := by
    ext i j
    rw [Matrix.conjTranspose_apply, hPdef, Matrix.map_apply, Matrix.map_apply, ← hGs i j, RingHom.comp_apply,
      RingHom.comp_apply]
    have h1 := host_emb_star D (v.embedding.comp (B.rho τ)) (gramN D 0 (Nat.zero_le _) j i)
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    rfl
  have hG' : G'ᵀ = P := by
    ext i j
    simp only [G', hPdef, Matrix.transpose_apply, Matrix.map_apply, RingHom.comp_apply]
    rw [hB, rhoC_conj, ← host_emb_star D (embS D v.embedding τ), hGs j i]
  have hdY : IsUnit Y.det := isUnit_iff_ne_zero.2 (Y_det_ne B v c τ)
  have hdYh : IsUnit Yᴴ.det := by rw [Matrix.det_conjTranspose]; exact hdY.star
  have hdP : IsUnit P.det := by rw [← hYP, Matrix.det_mul]; exact hdYh.mul hdY
  have key : Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ = 1 := by
    rw [hG', Zc, ← hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP]
    calc Y * P⁻¹ * P * (P⁻¹ * Yᴴ) = Y * (P⁻¹ * P) * P⁻¹ * Yᴴ := by simp only [Matrix.mul_assoc]
      _ = Y * P⁻¹ * Yᴴ := by rw [Matrix.nonsing_inv_mul _ hdP, Matrix.mul_one]
      _ = Y * (Y⁻¹ * (Yᴴ)⁻¹) * Yᴴ := by rw [← hYP, Matrix.mul_inv_rev]
      _ = (Y * Y⁻¹) * ((Yᴴ)⁻¹ * Yᴴ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdY, Matrix.nonsing_inv_mul _ hdYh, Matrix.mul_one]
  have ht : ((Zc B v c τ)ᵀ)ᴴ * G' * (Zc B v c τ)ᵀ = (Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rfl
  rw [ht, key, Matrix.transpose_one]

end Formalism.L2.GlobalTheoryTheory.ColValS
