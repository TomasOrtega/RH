import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Establish `e : f = fun a => ∑ i, (Pi.single i (f a i) : ι → E)`. Use function extensionality and compare the values at `a`. Rewrite using `[Finset.univ_sum_single]`. Rewrite using `[e]`.

Use `Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(continuous_single (A := fun _ : ι => E) i).comp_aestronglyMeasurable (hf i)`.
-/
theorem aesm_pi_of_finite {α ι E : Type} [MeasurableSpace α] {μ : Measure α} [Finite ι] [NormedAddCommGroup E]
    (f : α → ι → E) (hf : ∀ i, AEStronglyMeasurable (fun a => f a i) μ) : AEStronglyMeasurable f μ := by
  classical
  have := Fintype.ofFinite ι
  have e : f = fun a => ∑ i, (Pi.single i (f a i) : ι → E) := by
    funext a; rw [Finset.univ_sum_single]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (continuous_single (A := fun _ : ι => E) i).comp_aestronglyMeasurable (hf i)

/- English proof (translation)
Establish `e : (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) = fun c => ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then (‖c (Fin.last r)‖ ^ 2 - TT) ^ (k - 1) else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2)))`. Use function extensionality and compare the values at `c`. Unfold `TBB.nPt D.ptGG`. Rewrite using `[Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt, Complex.normSq_eq_norm_sq]`. Unfold `TBB.bigPt`.

Rewrite using `[Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]`. Rewrite using `[e]`. Use `Finset.measurable_prod _ fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`. Use `fun_prop`.

Conclude with `((measurable_pi_apply i).norm).pow_const _`.
-/
theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) = fun c =>
      ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then (‖c (Fin.last r)‖ ^ 2 - TT) ^ (k - 1)
        else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
    funext c
    unfold TBB.nPt D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt, Complex.normSq_eq_norm_sq]
    unfold TBB.bigPt
    rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  rw [e]
  refine Finset.measurable_prod _ fun i _ => ?_
  split_ifs
  · fun_prop
  · exact ((measurable_pi_apply i).norm).pow_const _

/- English proof (translation)
Establish `e : (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) = fun c => ‖∏ i, c i‖ ^ 2 / (‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2)`. Use function extensionality and compare the values at `c`. Use `show Top.wPt TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _`. Unfold `Top.wPt D.ptG`. Rewrite using `[Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]`.

Rewrite using `[e]`. Use `Measurable.div ?_ ?_` and prove the remaining obligations. Conclude with `(by fun_prop : Continuous fun c : Fin (r + 1) → ℂ => ‖∏ i, c i‖ ^ 2).measurable`. Conclude with `(by fun_prop : Continuous fun c : Fin (r + 1) → ℂ => ‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2).measurable`.
-/
theorem measurable_wPt_bigPt (r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) = fun c =>
      ‖∏ i, c i‖ ^ 2 / (‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2) := by
    funext c
    show Top.wPt TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold Top.wPt D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [e]
  refine Measurable.div ?_ ?_
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ => ‖∏ i, c i‖ ^ 2).measurable
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ =>
      ‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2).measurable

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p Cb H w hD hw hH`. Unfold `tv`. Use `(PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable (aesm_pi_of_finite _ fun x => ?_)` and prove the remaining obligations. Establish `hV` using `GlobalTheory.bigCell_vector_aestronglyMeasurable Wp Wq P p _ (GlobalTheory.liftedWord_continuousOn_GPos Wp Wq P p Cb w x.1 H hD hw hH)`. Establish `hc : Continuous fun X : Wq →L[ℂ] Wp => B.hsVec ((p.TP.E x.2).comp X)`.

Unfold `B.hsVec`. Use `(PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)` and prove the remaining obligations. Conclude with `(p.TP.E x.2).continuous.comp (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous`. Use `AEStronglyMeasurable.smul (f := fun c : Fin (P.r + 1) → ℂ => ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) * Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ)) ?_ (hc.comp_aestronglyMeasurable hV)` and prove the remaining obligations. Use `(Complex.measurable_ofReal.comp ?_).aestronglyMeasurable` and prove the remaining obligations.

Use `(measurable_nPt_bigPt _ _ _).sqrt.mul ?_` and prove the remaining obligations. Unfold `Top.dH`. Conclude with `(((measurable_wPt_bigPt _ _).pow_const _).mul_const _).sqrt`.
-/
theorem aestronglyMeasurable_tv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) H →
    AEStronglyMeasurable (tv p H w) volume := by
  intro Wp Wq _ _ _ _ _ _ P p Cb H w hD hw hH
  unfold tv
  refine (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable (aesm_pi_of_finite _ fun x => ?_)
  have hV := GlobalTheory.bigCell_vector_aestronglyMeasurable Wp Wq P p _ (GlobalTheory.liftedWord_continuousOn_GPos Wp Wq P p Cb w x.1 H hD hw hH)
  have hc : Continuous fun X : Wq →L[ℂ] Wp => B.hsVec ((p.TP.E x.2).comp X) := by
    unfold B.hsVec
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (p.TP.E x.2).continuous.comp
      (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  refine AEStronglyMeasurable.smul (f := fun c : Fin (P.r + 1) → ℂ =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ)) ?_ (hc.comp_aestronglyMeasurable hV)
  refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
  refine (measurable_nPt_bigPt _ _ _).sqrt.mul ?_
  unfold Top.dH
  exact (((measurable_wPt_bigPt _ _).pow_const _).mul_const _).sqrt

end GlobalTheory.TopVec
