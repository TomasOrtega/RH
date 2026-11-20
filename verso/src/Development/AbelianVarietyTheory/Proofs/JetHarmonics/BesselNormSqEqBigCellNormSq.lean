import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.jN2_eq_normSq_base

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

/- English proof (translation)
Use `set T := Tz P.k P.r p.T.base.z with hT`. Use `set T' := Tz P.k P.r p.T.base.z' with hT'`. Establish `hk : 2 ≤ P.k` using `p.hl.2.2`. Establish `hTT : 0 < T * T'` using `mul_pos p.T.base.T_pos p.T.base.T'_pos`. Establish `hw'` using `hw`.

Unfold `bcWeight at hw'`. Use `split_ifs at hw' with hle`. Establish `hprod` using `left_ne_zero_of_mul hw'`. Establish `hgg` using `right_ne_zero_of_mul hw'`. Establish `hlt : T * T' < Complex.normSq (c (Fin.last P.r))`.

Break down `hle.lt_or_eq with h | h` into its components or cases. Conclude with `h`. Use the proof step `exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]`. Establish `hc : ∀ a : Fin P.r, c a.castSucc ≠ 0`. Introduce `a ha`.

Apply `hprod` to reduce the goal to its premises. Use `Finset.prod_eq_zero (Finset.mem_univ a) ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[ha, norm_zero, zero_pow]`. Unfold `Mdim`.

Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hlast : c (Fin.last P.r) ≠ 0`. Introduce `h0`. Rewrite `hlt` using `[h0, Complex.normSq_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : ∀ a, c a ≠ 0`. Introduce `a`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact hlast`.

Consider the case `cast i => exact hc i`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Use `show 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)`. Unfold `D.ptG`. Rewrite using `[Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]`.

Establish `hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc)` using `Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left hlt hp]`. Conclude with `absurd rfl hw'`.
-/
theorem good_of_weight_ne_zero (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ)
    (hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) ≠ 0) :
    (∀ a, c a ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  have hk : 2 ≤ P.k := p.hl.2.2
  have hTT : 0 < T * T' := mul_pos p.T.base.T_pos p.T.base.T'_pos
  have hw' := hw
  unfold bcWeight at hw'
  split_ifs at hw' with hle
  · have hprod := left_ne_zero_of_mul hw'
    have hgg := right_ne_zero_of_mul hw'
    have hlt : T * T' < Complex.normSq (c (Fin.last P.r)) := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]
    have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := by
      intro a ha
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      dsimp only
      rw [ha, norm_zero, zero_pow]
      unfold Mdim; have := a.isLt; omega
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    refine ⟨hd, ?_⟩
    show 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
      Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
    nlinarith [mul_lt_mul_of_pos_left hlt hp]
  · exact absurd rfl hw'

/- English proof (translation)
Distinguish the cases in `h : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)`. Take `⟨hl, hG⟩` from `h`. Establish `hd : ∀ a, c a ≠ 0` using `fun a => (hl.1 (1, c a) (by unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a, rfl⟩)).2`. Establish `hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)` using `hG`. Establish `hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))` using `Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG'`.

Rewrite using `[TBBx2.Tri.Ew_top p F hl, hsVec_norm_V_bigPt p F c hd hG]`. Establish `hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') ((fun j => c j.castSucc), c (Fin.last P.r))` using `nPt_bigPt P.k P.r _ _ c hζ.le`. Rewrite using `[hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]`. Establish `hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') ((fun j => c j.castSucc), c (Fin.last P.r)) = 0`. Assume the negation of the conclusion as `hw`.

Take `⟨hd, hG⟩` from `good_of_weight_ne_zero p c hw`. Conclude with `h ⟨Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd, hG⟩`. Rewrite using `[TBBx4.ew_zero_of p F h, hw, zero_mul]`.
-/
theorem pt_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
    bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) *
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc)
        (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2 := by
  by_cases h : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  · obtain ⟨hl, hG⟩ := h
    have hd : ∀ a, c a ≠ 0 := fun a =>
      (hl.1 (1, c a) (by unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a, rfl⟩)).2
    have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := hG
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG'
    rw [TBBx2.Tri.Ew_top p F hl, hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := nPt_bigPt P.k P.r _ _ c hζ.le
    rw [hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]
  · have hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) = 0 := by
      by_contra hw
      obtain ⟨hd, hG⟩ := good_of_weight_ne_zero p c hw
      exact h ⟨Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd, hG⟩
    rw [TBBx4.ew_zero_of p F h, hw, zero_mul]

/- English proof (translation)
Introduce `P Wp Wq _ _ _ _ _ _ p F`. Set `e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ` to `(MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm`. Establish `hmp : MeasurePreserving e volume volume` using `(Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))`. Establish `he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r))`. Introduce `c`.

Simplify using `[e, MeasurableEquiv.piFinSuccAbove]`. Both sides reduce to the same expression. Unfold `B.normSq jNormSq`. Rewrite using `[← hmp.lintegral_comp_emb e.measurableEmbedding]`. Unfold `TBB.jN2`.

Use `lintegral_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[he c, pt_eq p F c]`. Both sides reduce to the same expression.
-/
theorem besselNormSq_eq_bigCellNormSq : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F := by
  intro P Wp Wq _ _ _ _ _ _ p F
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  unfold B.normSq jNormSq
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
  unfold TBB.jN2
  refine lintegral_congr fun c => ?_
  rw [he c, pt_eq p F c]
  rfl

end GlobalTheory.jN2_eq_normSq_base
