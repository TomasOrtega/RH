import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FlagExtensionRegularity
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianSumFrames
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TraceEqSumPlaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SpanPreservation

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.FormRegularity

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames
  Formalism.MainNotions.S.Lat

section Mat

variable {r : ℕ}

def sgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.1)

/- English proof (translation)
Rewrite using `[sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem sgn_sq : sgn r * sgn r = 1 := by
  rw [sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[ZhatO, sgn, Matrix.mul_diagonal, mul_comm]`.
-/
theorem zhatO_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ZhatO Z = Z * sgn r := by
  ext a b
  rw [ZhatO, sgn, Matrix.mul_diagonal, mul_comm]

/- English proof (translation)
Introduce `i j`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, (h i j).1 hij, map_zero]`. Rewrite using `[Matrix.map_apply, (h i j).2 hij, map_one]`.
-/
theorem isLoUni_map {K : Type*} [Field K] (ψ : K →+* ℂ) {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : IsLoUni L) : IsLoUni (L.map ψ) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, map_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, map_one]

/- English proof (translation)
Introduce `i j`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, (h i j).1 hij, star_zero]`. Rewrite using `[Matrix.map_apply, (h i j).2 hij, star_one]`.
-/
theorem isLoUni_star {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsLoUni L) : IsLoUni (L.map star) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, star_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, star_one]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.transpose_apply, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[(h j i).1 hij]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `hij` using the available equality. Rewrite using `[(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem isLoUni_sgnT {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsUpUni U) :
    IsLoUni (sgn r * U * sgn r)ᵀ := by
  intro i j
  simp only [Matrix.transpose_apply, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [(h j i).1 hij]; ring
  · subst hij
    rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular L (fun i j hij => (h i j).1 (OrderDual.toDual_lt_toDual.1 hij))]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`.
-/
theorem det_lo {K : Type*} [Field K] {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => (h i j).1 (OrderDual.toDual_lt_toDual.1 hij))]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`.
-/
theorem det_up {K : Type*} [Field K] {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

/- English proof (translation)
Introduce `i j`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, (h i j).1 hij, map_zero]`. Rewrite using `[Matrix.map_apply, (h i j).2 hij, map_one]`.
-/
theorem isUpUni_map {K : Type*} [Field K] (ψ : K →+* ℂ) {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : IsUpUni U) : IsUpUni (U.map ψ) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.map_apply, (h i j).1 hij, map_zero]
  · rw [Matrix.map_apply, (h i j).2 hij, map_one]

/- English proof (translation)
The claim follows from `((Matrix.isUnit_iff_isUnit_det L).2 (Ne.isUnit hL)).mul_left_cancel (((Matrix.isUnit_iff_isUnit_det U).2 (Ne.isUnit hU)).mul_right_cancel h)`.
-/
theorem cancel {L A B U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hL : L.det ≠ 0) (hU : U.det ≠ 0)
    (h : L * A * U = L * B * U) : A = B :=
  ((Matrix.isUnit_iff_isUnit_det L).2 (Ne.isUnit hL)).mul_left_cancel
    (((Matrix.isUnit_iff_isUnit_det U).2 (Ne.isUnit hU)).mul_right_cancel h)

/- English proof (translation)
Unfold `Formalism.L2.SG.PairVal.sgLo`. Rewrite using `[Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (by simp)]`. Both sides reduce to the same expression.
-/
theorem sgLo_eq {K : Type} [Field K] (L : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.L2.SG.PairVal.sgLo L = ∑ a : Fin r, L a.succ a.castSucc := by
  unfold Formalism.L2.SG.PairVal.sgLo
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (by simp)]
  rfl

/- English proof (translation)
Unfold `Formalism.L2.SG.PairVal.sgUp`. Rewrite using `[Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (by simp)]`. Both sides reduce to the same expression.
-/
theorem sgUp_eq {K : Type} [Field K] (U : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.L2.SG.PairVal.sgUp U = ∑ a : Fin r, U a.castSucc a.succ := by
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (by simp)]
  rfl

/- English proof (translation)
Establish `h : r - a.castSucc.1 = (r - a.succ.1) + 1`. Simplify using `only [Fin.coe_castSucc, Fin.val_succ]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h, ← pow_add]`. Conclude with `Odd.neg_one_pow ⟨r - a.succ.1, by ring⟩`.
-/
theorem sgn_adj (a : Fin r) : (-1 : ℂ) ^ (r - a.castSucc.1) * (-1 : ℂ) ^ (r - a.succ.1) = -1 := by
  have h : r - a.castSucc.1 = (r - a.succ.1) + 1 := by
    simp only [Fin.coe_castSucc, Fin.val_succ]; omega
  rw [h, ← pow_add]
  exact Odd.neg_one_pow ⟨r - a.succ.1, by ring⟩

end Mat

/- English proof (translation)
Unfold `Formalism.L2.SG.PairVal.psiInf`. Rewrite using `[← Complex.exp_neg, map_neg]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psiInf_neg {E : Type} [Field E] [NumberField E] (g : ℕ) (x : E) :
    Formalism.L2.SG.PairVal.psiInf g (-x) = (Formalism.L2.SG.PairVal.psiInf g x)⁻¹ := by
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [← Complex.exp_neg, map_neg]
  congr 1
  push_cast
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Simplify using `only [ZX, frm, FlagExtensionRegularity.famSc_one]`.
-/
theorem zx_eq (u u' : D.what₂.Word) (δ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    ZX X u u' 1 δ v = Zhat (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
      (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (δ v)) := by
  simp only [ZX, frm, FlagExtensionRegularity.famSc_one]

/- English proof (translation)
Introduce `v x _`. Simplify using `[uMat]`.
-/
theorem one_mem_HsetU (u : D.what₂.Word) : (1 : X.B.I.Ginf) ∈ HsetU X u := by
  intro v x _
  simp [uMat]

/- English proof (translation)
Establish `hfr` using `fun v => HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v`. Establish `hrc : ∀ v a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (uMat (s v)) a = P v a.succ a.castSucc` using `fun v a => HermitianSumRootCoordinateFrames.RootCoordFrame_holds _ _ _ _ _ _ (hfr v).2.2.2.1 (fun a => ((hfr v).2.2.2.2.1 a).2) _ _ (hP v) a`. Unfold `HidaSetting.psiInfU psiInf psiR`. Simplify using `only [hrc, hy]`. Rewrite using `[PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm y), RingEquiv.apply_symm_apply]`.
-/
theorem psi_of_frame (u : D.what₂.Word) (s : X.B.I.Ginf)
    (P : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ)
    (hP : ∀ v a, uMat (s v) *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) a =
       ∑ c, P v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) c)
    (y : D.host.E) (hy : ∀ v, ∑ a : Fin D.R.rS, (P v a.succ a.castSucc + star (P v a.succ a.castSucc)) =
       X.B.I.φ v (X.ιE.symm y) + star (X.B.I.φ v (X.ιE.symm y))) :
    X.psiInfU u s = Formalism.L2.SG.PairVal.psiInf X.B.g y := by
  have hfr := fun v => HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v
  have hrc : ∀ v a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (uMat (s v)) a = P v a.succ a.castSucc := fun v a =>
    HermitianSumRootCoordinateFrames.RootCoordFrame_holds _ _ _ _ _ _ (hfr v).2.2.2.1 (fun a => ((hfr v).2.2.2.2.1 a).2) _ _ (hP v) a
  unfold HidaSetting.psiInfU psiInf psiR
  simp only [hrc, hy]
  rw [PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm y), RingEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `hFT t w L U hreg hLo hUp hZ`. Establish `hOOt` using `FlagExtensionRegularity.OOtReg_holds X u u' F0 F0' what₂ rows' hFT t hreg`. Set `ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ` to `fun v => (X.B.I.φ v).comp X.ιE.symm.toRingHom`. Set `P : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ` to `fun v => (L.map (ψ v)).map star`. Set `P' : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ` to `fun v => (sgn D.R.rS * U.map (ψ v) * sgn D.R.rS)ᵀ`.

Establish `hzz : ∀ (w' : D.what₂.Word) v, hJ (X.B.I.ε v) (rv X.B.I v (X.zR w')) (rv X.B.I v (X.zR w')) ≠ 0`. Introduce `w' v`. Rewrite using `[(HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.1]`. Conclude with `neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.2)`. Establish `hs : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v), InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s) ∧ ∀ a, uMat s *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) a = ∑ c, P v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) c` using `fun v => hF1 X.B.I.n D.R.rS (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.1 (HermitianSumRootCoordinateFrames. …`.

Establish `hs' : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v), InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat s) ∧ ∀ a, uMat s *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) a = ∑ c, P' v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) …` using `fun v => hF1 X.B.I.n D.R.rS (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.1 (HermitianSumRootCoordinateFram …`. Use `choose s hsN hsP using hs`. Use `choose s' hs'N hs'P using hs'`. Establish `hsN' : s ∈ X.NinfU u` using `fun v => hsN v`. Establish `hs'N' : s' ∈ X.NinfU u'` using `fun v => hs'N v`.

Establish `hsS : s ∈ X.SinfU u` using `fun v => (hsN v).1`. Establish `hs'S : s' ∈ X.SinfU u'` using `fun v => (hs'N v).1`. Establish `hPt : IsPtRep X u u' w (s * t.pt.1 * s'⁻¹)`. Introduce `v`. Establish `hg : s⁻¹ * (s * t.pt.1 * s'⁻¹) * s' = t.pt.1` using `by group`.

Establish `h4` using `HermitianSumRootCoordinateFrames.ZhatNAct_holds _ _ (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (s v)) (uMat (s⁻¹ v)) (uMat (s' v)) (uMat ((s * t.pt.1 * s'⁻¹) v)) (P v) (P' v) (InfCut.uMa …`. Establish `hγv : uMat (s⁻¹ v) * uMat ((s * t.pt.1 * s'⁻¹) v) * uMat (s' v) = uMat (t.pt.1 v)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [uMat, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]`. Use `_ = uMat (t.pt.1 v) := by rw [hg]`.

Rewrite `h4` using `[hγv, ← zx_eq, ← zx_eq]`. Establish `h5 : ZhatO (ZX X u u' 1 t.pt.1 v) = (L * ptMat w * U).map (ψ v)` using `hZ v`. Rewrite `h5` using `[Matrix.map_mul, Matrix.map_mul, zhatO_eq, h4]`. Establish `hPs : (P v).map star = L.map (ψ v)`. Use extensionality with `i j`.

Simplify using `only [P, Matrix.map_apply, star_star]`. Establish `hPt' : (P' v)ᵀ = sgn D.R.rS * U.map (ψ v) * sgn D.R.rS` using `Matrix.transpose_transpose _`. Rewrite `h5` using `[hPs, hPt']`. Establish `h6 : L.map (ψ v) * ZhatO (ZX X u u' 1 (s * t.pt.1 * s'⁻¹) v) * U.map (ψ v) = L.map (ψ v) * ptC X v w * U.map (ψ v)`. Use `Eq.trans ?_ h5` and prove the remaining obligations.

Rewrite using `[zhatO_eq]`. Simplify using `only [Matrix.mul_assoc, sgn_sq, Matrix.mul_one]`. Conclude with `cancel (by rw [det_lo (isLoUni_map _ hLo)]; exact one_ne_zero) (by rw [det_up (isUpUni_map _ hUp)]; exact one_ne_zero) h6`. Establish `hpi1 : ∀ w', X.piU w' 1 = 1` using `fun w' => (X.piU_rep w').1`. Establish `hpis : X.piU u s = 1` using `(X.piU_rep u).2.2.2.1 s hsN'`.

Establish `hpis' : X.piU u' s'⁻¹ = 1`. Establish `hm` using `(X.piU_rep u').2.1 s'⁻¹ (InfCut.sinfU_inv X u' hs'S) s' hs'S`. Rewrite `hm` using `[inv_mul_cancel, hpi1, (X.piU_rep u').2.2.2.1 s' hs'N', mul_one]`. Conclude with `hm.symm`. Establish `hEq` using `InfCut.ooEquivar X u u' t.pt.1 s hsS s' hs'S`.

Rewrite `hEq` using `[hpis, hpis']`. Establish `hψu : X.psiInfU u s = Formalism.L2.SG.PairVal.psiInf X.B.g (Formalism.L2.SG.PairVal.sgLo L)`. Use `psi_of_frame X u s P hsP _ fun v => ?_` and prove the remaining obligations. Simplify using `only [P, ψ, Matrix.map_apply, star_star, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, sgLo_eq, map_sum, star_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => add_comm _ _`.

Establish `hψu' : X.psiInfU u' s' = Formalism.L2.SG.PairVal.psiInf X.B.g (-Formalism.L2.SG.PairVal.sgUp U)`. Use `psi_of_frame X u' s' P' hs'P _ fun v => ?_` and prove the remaining obligations. Establish `h1 : ∀ a : Fin D.R.rS, P' v a.succ a.castSucc = -(ψ v (U a.castSucc a.succ))`. Introduce `a`. Simplify using `only [P', Matrix.transpose_apply, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]`.

Take the linear combination `(ψ v (U a.castSucc a.succ)) * sgn_adj a`. Simplify using `only [h1, ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, sgUp_eq, map_neg, map_sum, star_neg, star_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib]`. Both sides reduce to the same expression. Establish `hgS : X.B.g = gS D` using `X.g_eq`. Establish `hne : ∀ x : D.host.E, Formalism.L2.SG.PairVal.psiInf (gS D) x ≠ 0` using `fun x => Complex.exp_ne_zero _`.

Establish `hprod : Formalism.L2.SG.PairVal.phasePair (gS D) L U * (X.psiInfU u s * conj (X.psiInfU u' s')) = 1`. Rewrite using `[hψu, hψu', psiInf_neg, Vanish.conj_inv_of_norm (Formalism.L2.SG.PairVal.norm_psiInf _ _), hgS]`. Unfold `Formalism.L2.SG.PairVal.phasePair`. Clear denominators, using `[hne]` for the nonvanishing conditions. Use `⟨s * t.pt.1 * s'⁻¹, hPt, 1, one_mem_HsetU X u, 1, one_mem_HsetU X u', s⁻¹, SpanPreservation.ninfU_inv X u hsN', s', hs'N', by group, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_one, hpi1, hpi1, hOOt, hEq]`. Use extensionality with `x`. Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, smul_smul, hprod, one_smul]`.
-/
theorem form_regular_of_realization (hF1 : NRealize) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)) :
    FormReg X u u' F0 F0' what₂ rows' := by
  intro hFT t w L U hreg hLo hUp hZ
  have hOOt := FlagExtensionRegularity.OOtReg_holds X u u' F0 F0' what₂ rows' hFT t hreg
  let ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => (X.B.I.φ v).comp X.ιE.symm.toRingHom
  let P : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v => (L.map (ψ v)).map star
  let P' : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
    fun v => (sgn D.R.rS * U.map (ψ v) * sgn D.R.rS)ᵀ
  have hzz : ∀ (w' : D.what₂.Word) v, hJ (X.B.I.ε v) (rv X.B.I v (X.zR w')) (rv X.B.I v (X.zR w')) ≠ 0 := by
    intro w' v
    rw [(HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.1]
    exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.2)
  have hs : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v),
      InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s) ∧
      ∀ a, uMat s *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) a =
        ∑ c, P v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) c := fun v =>
    hF1 X.B.I.n D.R.rS (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.1
      (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.2.1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.2.2.2.1 (hzz u v) (P v)
      (isLoUni_star (isLoUni_map _ hLo))
  have hs' : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v),
      InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat s) ∧
      ∀ a, uMat s *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) a =
        ∑ c, P' v a c • fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) c := fun v =>
    hF1 X.B.I.n D.R.rS (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u')) (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.1
      (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.2.1 (HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.2.2.2.1 (hzz u' v) (P' v)
      (isLoUni_sgnT (isUpUni_map _ hUp))
  choose s hsN hsP using hs
  choose s' hs'N hs'P using hs'
  have hsN' : s ∈ X.NinfU u := fun v => hsN v
  have hs'N' : s' ∈ X.NinfU u' := fun v => hs'N v
  have hsS : s ∈ X.SinfU u := fun v => (hsN v).1
  have hs'S : s' ∈ X.SinfU u' := fun v => (hs'N v).1

  have hPt : IsPtRep X u u' w (s * t.pt.1 * s'⁻¹) := by
    intro v
    have hg : s⁻¹ * (s * t.pt.1 * s'⁻¹) * s' = t.pt.1 := by group
    have h4 := HermitianSumRootCoordinateFrames.ZhatNAct_holds _ _ (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
      (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (s v)) (uMat (s⁻¹ v)) (uMat (s' v))
      (uMat ((s * t.pt.1 * s'⁻¹) v)) (P v) (P' v) (InfCut.uMat_inv_mul' (s v)) (hJ_map _ (s v).2) (hsP v) (hs'P v)
    have hγv : uMat (s⁻¹ v) * uMat ((s * t.pt.1 * s'⁻¹) v) * uMat (s' v) = uMat (t.pt.1 v) := by
      calc uMat (s⁻¹ v) * uMat ((s * t.pt.1 * s'⁻¹) v) * uMat (s' v)
          = uMat ((s⁻¹ * (s * t.pt.1 * s'⁻¹) * s') v) := by
            simp only [uMat, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]
        _ = uMat (t.pt.1 v) := by rw [hg]
    rw [hγv, ← zx_eq, ← zx_eq] at h4
    have h5 : ZhatO (ZX X u u' 1 t.pt.1 v) = (L * ptMat w * U).map (ψ v) := hZ v
    rw [Matrix.map_mul, Matrix.map_mul, zhatO_eq, h4] at h5
    have hPs : (P v).map star = L.map (ψ v) := by
      ext i j
      simp only [P, Matrix.map_apply, star_star]
    have hPt' : (P' v)ᵀ = sgn D.R.rS * U.map (ψ v) * sgn D.R.rS := Matrix.transpose_transpose _
    rw [hPs, hPt'] at h5
    have h6 : L.map (ψ v) * ZhatO (ZX X u u' 1 (s * t.pt.1 * s'⁻¹) v) * U.map (ψ v) =
        L.map (ψ v) * ptC X v w * U.map (ψ v) := by
      refine Eq.trans ?_ h5
      rw [zhatO_eq]
      simp only [Matrix.mul_assoc, sgn_sq, Matrix.mul_one]
    exact cancel (by rw [det_lo (isLoUni_map _ hLo)]; exact one_ne_zero)
      (by rw [det_up (isUpUni_map _ hUp)]; exact one_ne_zero) h6

  have hpi1 : ∀ w', X.piU w' 1 = 1 := fun w' => (X.piU_rep w').1
  have hpis : X.piU u s = 1 := (X.piU_rep u).2.2.2.1 s hsN'
  have hpis' : X.piU u' s'⁻¹ = 1 := by
    have hm := (X.piU_rep u').2.1 s'⁻¹ (InfCut.sinfU_inv X u' hs'S) s' hs'S
    rw [inv_mul_cancel, hpi1, (X.piU_rep u').2.2.2.1 s' hs'N', mul_one] at hm
    exact hm.symm
  have hEq := InfCut.ooEquivar X u u' t.pt.1 s hsS s' hs'S
  rw [hpis, hpis'] at hEq
  have hψu : X.psiInfU u s = Formalism.L2.SG.PairVal.psiInf X.B.g (Formalism.L2.SG.PairVal.sgLo L) := by
    refine psi_of_frame X u s P hsP _ fun v => ?_
    simp only [P, ψ, Matrix.map_apply, star_star, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
      sgLo_eq, map_sum, star_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => add_comm _ _
  have hψu' : X.psiInfU u' s' = Formalism.L2.SG.PairVal.psiInf X.B.g (-Formalism.L2.SG.PairVal.sgUp U) := by
    refine psi_of_frame X u' s' P' hs'P _ fun v => ?_
    have h1 : ∀ a : Fin D.R.rS, P' v a.succ a.castSucc = -(ψ v (U a.castSucc a.succ)) := by
      intro a
      simp only [P', Matrix.transpose_apply, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
      linear_combination (ψ v (U a.castSucc a.succ)) * sgn_adj a
    simp only [h1, ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, sgUp_eq, map_neg, map_sum,
      star_neg, star_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rfl
  have hgS : X.B.g = gS D := X.g_eq
  have hne : ∀ x : D.host.E, Formalism.L2.SG.PairVal.psiInf (gS D) x ≠ 0 := fun x => Complex.exp_ne_zero _
  have hprod : Formalism.L2.SG.PairVal.phasePair (gS D) L U * (X.psiInfU u s * conj (X.psiInfU u' s')) = 1 := by
    rw [hψu, hψu', psiInf_neg, Vanish.conj_inv_of_norm (Formalism.L2.SG.PairVal.norm_psiInf _ _), hgS]
    unfold Formalism.L2.SG.PairVal.phasePair
    field_simp [hne]
  refine ⟨s * t.pt.1 * s'⁻¹, hPt, 1, one_mem_HsetU X u, 1, one_mem_HsetU X u', s⁻¹, SpanPreservation.ninfU_inv X u hsN', s', hs'N',
    by group, ?_⟩
  rw [inv_one, hpi1, hpi1, hOOt, hEq]
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, smul_smul,
    hprod, one_smul]

end Main

end Formalism.L2.SG.RealObj.FormRegularity
