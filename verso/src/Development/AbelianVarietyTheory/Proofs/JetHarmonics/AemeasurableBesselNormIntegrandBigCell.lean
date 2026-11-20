import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P in

/- English proof (translation)
Establish `hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)` using `Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd`. Establish `hc : ∀ a : Fin P.r, c a.castSucc ≠ 0` using `fun a => hd _`. Rewrite using `[TBBx2.Tri.Ew_top p F hl]`. Use `split_ifs with hlt`. Establish `hG : 0 < TBB.Gp p (TBB.bigPt P.r c)` using `by show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)`.

Unfold `D.ptG`. Rewrite using `[Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]`. Establish `hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc)` using `Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left hlt hp]`. Establish `hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') ((fun j => c j.castSucc), c (Fin.last P.r))` using `CutBP.nPt_bigPt P.k P.r _ _ c hlt.le`.

Establish `hq : ((fun j => c j.castSucc), c (Fin.last P.r)) ∈ B7.Q0 p.T.base` using `⟨hc, hlt⟩`. Rewrite using `[CutBP.hsVec_norm_V_bigPt p F c hd hG, hn, Real.mul_self_sqrt (CutBP.bcWeight_nonneg0 _ _ _ _ _), B7.JM_eq p.T.base F (1, 1) hq, bessel_function_trivial_index P.k P.r Wp Wq p.T.base F, B7.hsL_apply]`. Both sides reduce to the same expression. Establish `hV : p.V F (TBB.bigPt P.r c) = 0` using `by show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = 0`. Unfold `D.vecV`.

Rewrite using `[dif_neg]`. Introduce and unpack `⟨-, hG⟩`. Conclude with `hlt (Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG)`. Rewrite using `[hV, TBBx2.Tri.hsVec_zero]`. Simplify using the standard rewrite rules.
-/
theorem bigCell_density_eq {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) (hd : ∀ a, c a ≠ 0) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
            ((fun j => c j.castSucc), c (Fin.last P.r)) *
          ‖B7.hsL (B7.JM p.T.base F (1, 1) ((fun j => c j.castSucc), c (Fin.last P.r)))‖ ^ 2
      else 0 := by
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
  have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
  rw [TBBx2.Tri.Ew_top p F hl]
  split_ifs with hlt
  · have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    have hq : ((fun j => c j.castSucc), c (Fin.last P.r)) ∈ B7.Q0 p.T.base := ⟨hc, hlt⟩
    rw [CutBP.hsVec_norm_V_bigPt p F c hd hG, hn, Real.mul_self_sqrt (CutBP.bcWeight_nonneg0 _ _ _ _ _),
      B7.JM_eq p.T.base F (1, 1) hq, bessel_function_trivial_index P.k P.r Wp Wq p.T.base F, B7.hsL_apply]
    rfl
  · have hV : p.V F (TBB.bigPt P.r c) = 0 := by
      show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = 0
      unfold D.vecV
      rw [dif_neg]
      rintro ⟨-, hG⟩
      exact hlt (Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG)
    rw [hV, TBBx2.Tri.hsVec_zero]
    simp

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P in

/- English proof (translation)
Introduce `P Wp Wq _ _ _ _ _ _ p F hF`. Establish `hq : Measurable fun c : Fin (P.r + 1) → ℂ => (((fun j => c j.castSucc), c (Fin.last P.r)) : (Fin P.r → ℂ) × ℂ)` using `by fun_prop`. Establish `hJ : StronglyMeasurable fun q : (Fin P.r → ℂ) × ℂ => B7.JM p.T.base F (1, 1) q` using `(B7.sm_JM p.T.base hF).comp_measurable measurable_prodMk_left`. Establish `hN : Measurable fun q : (Fin P.r → ℂ) × ℂ => ‖B7.hsL (B7.JM p.T.base F (1, 1) q)‖` using `((B7.hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable hJ).norm.measurable`. Establish `hm : Measurable fun c : Fin (P.r + 1) → ℂ => if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') ((fun j => c j.castSucc), c (Fin.last P.r)) * ‖B7.hsL (B7.JM p.T.base F (1, 1) …`.

Use `Measurable.ite ?_ ?_ measurable_const` and prove the remaining obligations. Conclude with `measurableSet_lt measurable_const (Complex.continuous_normSq.measurable.comp (measurable_pi_apply _))`. Conclude with `((B7.measurable_bcWeight _ _).comp hq).mul ((hN.comp hq).pow_const 2)`. Establish `hae : ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ a, c a ≠ 0`. Rewrite using `[ae_all_iff]`.

Introduce `a`. Conclude with `Measure.ae_eval_ne (fun _ => (volume : Measure ℂ)) a 0`. Use `(ENNReal.measurable_ofReal.comp hm).aemeasurable.congr ?_` and prove the remaining obligations. Use `filter_upwards [hae] with c hc`. Rewrite using `[bigCell_density_eq p F c hc]`.

Both sides reduce to the same expression.
-/
theorem bigCell_density_aemeasurable :
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn F (B.GV P.k P.r) →
      AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro P Wp Wq _ _ _ _ _ _ p F hF
  have hq : Measurable fun c : Fin (P.r + 1) → ℂ =>
      (((fun j => c j.castSucc), c (Fin.last P.r)) : (Fin P.r → ℂ) × ℂ) := by fun_prop
  have hJ : StronglyMeasurable fun q : (Fin P.r → ℂ) × ℂ => B7.JM p.T.base F (1, 1) q :=
    (B7.sm_JM p.T.base hF).comp_measurable measurable_prodMk_left
  have hN : Measurable fun q : (Fin P.r → ℂ) × ℂ => ‖B7.hsL (B7.JM p.T.base F (1, 1) q)‖ :=
    ((B7.hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable hJ).norm.measurable
  have hm : Measurable fun c : Fin (P.r + 1) → ℂ =>
      if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
            ((fun j => c j.castSucc), c (Fin.last P.r)) *
          ‖B7.hsL (B7.JM p.T.base F (1, 1) ((fun j => c j.castSucc), c (Fin.last P.r)))‖ ^ 2
      else 0 := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const
        (Complex.continuous_normSq.measurable.comp (measurable_pi_apply _))
    · exact ((B7.measurable_bcWeight _ _).comp hq).mul ((hN.comp hq).pow_const 2)
  have hae : ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ a, c a ≠ 0 := by
    rw [ae_all_iff]
    intro a
    exact Measure.ae_eval_ne (fun _ => (volume : Measure ℂ)) a 0
  refine (ENNReal.measurable_ofReal.comp hm).aemeasurable.congr ?_
  filter_upwards [hae] with c hc
  rw [bigCell_density_eq p F c hc]
  rfl

end GlobalTheory
