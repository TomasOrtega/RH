import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGCut

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ENNReal

noncomputable section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

/- English proof (translation)
Use `set T := Tz P.k P.r p.T.base.z with hT`. Use `set T' := Tz P.k P.r p.T.base.z' with hT'`. Establish `hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)` using `Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd`. Establish `hGf : TBB.Gp p (TBB.bigPt P.r c) = Complex.normSq (∏ i : Fin P.r, c i.castSucc) * Complex.normSq (c (Fin.last P.r)) - T * T' * Complex.normSq (∏ i : Fin P.r, c i.castSucc)` using `by show D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _`. Unfold `D.ptG`.

Rewrite using `[Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]`. Establish `hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc)` using `Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hd _)`. Distinguish the cases in `hlt : T * T' < Complex.normSq (c (Fin.last P.r))`. Establish `hG : 0 < TBB.Gp p (TBB.bigPt P.r c)`. Rewrite using `[hGf]`.

Use polynomial arithmetic with `[mul_lt_mul_of_pos_left hlt hp]`. Rewrite using `[TBBx2.Tri.Ew_top p F hl, CutBP.hsVec_norm_V_bigPt p F c hd hG]`. Establish `hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r))` using `CutBP.nPt_bigPt P.k P.r T T' c hlt.le`. Rewrite using `[hn, Real.mul_self_sqrt (CutBP.bcWeight_nonneg0 _ _ _ _ _)]`. Establish `hw : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0`.

Unfold `bcWeight`. Use `split_ifs with hle`. Establish `he : Complex.normSq (c (Fin.last P.r)) = T * T'` using `le_antisymm (not_lt.1 hlt) hle dsimp only`. Rewrite using `[he, sub_self, zero_pow (by have := p.hl.2.2; omega), mul_zero]`. Both sides reduce to the same expression.

Establish `hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c)`. Rewrite using `[hGf]`. Use `push Not`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (not_lt.1 hlt) hp.le]`. Establish `hV : p.V F (TBB.bigPt P.r c) = 0` using `by show D.vecV p.T.base p.ν' p.m₀ F (TBB.bigPt P.r c) = 0`.

Unfold `D.vecV`. Rewrite using `[dif_neg (fun h => hG h.2)]`. Rewrite using `[hw, zero_mul, TBBx2.Tri.Ew_top p F hl, hV, TBBx2.Tri.hsVec_zero, norm_zero]`. Simplify using the standard rewrite rules.
-/
theorem pt_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, c a ≠ 0) :
    ENNReal.ofReal (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) *
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc) (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2) =
    ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c)) := by
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
  have hGf : TBB.Gp p (TBB.bigPt P.r c) =
      Complex.normSq (∏ i : Fin P.r, c i.castSucc) * Complex.normSq (c (Fin.last P.r)) -
        T * T' * Complex.normSq (∏ i : Fin P.r, c i.castSucc) := by
    show D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
  have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hd _)
  by_cases hlt : T * T' < Complex.normSq (c (Fin.last P.r))
  · have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [hGf]; nlinarith [mul_lt_mul_of_pos_left hlt hp]
    rw [TBBx2.Tri.Ew_top p F hl, CutBP.hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) :=
      CutBP.nPt_bigPt P.k P.r T T' c hlt.le
    rw [hn, Real.mul_self_sqrt (CutBP.bcWeight_nonneg0 _ _ _ _ _)]
  · have hw : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0 := by
      unfold bcWeight
      split_ifs with hle
      · have he : Complex.normSq (c (Fin.last P.r)) = T * T' := le_antisymm (not_lt.1 hlt) hle
        dsimp only
        rw [he, sub_self, zero_pow (by have := p.hl.2.2; omega), mul_zero]
      · rfl
    have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [hGf]; push Not; nlinarith [mul_le_mul_of_nonneg_left (not_lt.1 hlt) hp.le]
    have hV : p.V F (TBB.bigPt P.r c) = 0 := by
      show D.vecV p.T.base p.ν' p.m₀ F (TBB.bigPt P.r c) = 0
      unfold D.vecV
      rw [dif_neg (fun h => hG h.2)]
    rw [hw, zero_mul, TBBx2.Tri.Ew_top p F hl, hV, TBBx2.Tri.hsVec_zero, norm_zero]
    simp

/- English proof (translation)
Introduce `P Wp Wq _ _ _ _ _ _ p F`. Unfold `B.normSq Formalism.QuantumDeterminants.jNormSq`. Set `e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ` to `(MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm`. Establish `hmp : MeasurePreserving e volume volume` using `(Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))`. Establish `he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r))`.

Introduce `c`. Simplify using `[e, MeasurableEquiv.piFinSuccAbove]`. Both sides reduce to the same expression. Rewrite using `[← hmp.lintegral_comp_emb e.measurableEmbedding]`. Unfold `TBB.jN2`.

Establish `hnull : ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ a, c a ≠ 0`. Rewrite using `[ae_all_iff]`. Introduce `a`. Rewrite using `[ae_iff]`. Simplify using `only [ne_eq, not_not]`.

Conclude with `Measure.pi_hyperplane _ a 0`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hnull] with c hc`. Rewrite using `[he c]`. Conclude with `(pt_eq p F c hc).symm`.
-/
theorem norm_square_transfer_identity_holds : NormSquareTransferIdentity := by
  intro P Wp Wq _ _ _ _ _ _ p F
  unfold B.normSq Formalism.QuantumDeterminants.jNormSq
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
  unfold TBB.jN2
  have hnull : ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ a, c a ≠ 0 := by
    rw [ae_all_iff]
    intro a
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact Measure.pi_hyperplane _ a 0
  refine lintegral_congr_ae ?_
  filter_upwards [hnull] with c hc
  rw [he c]
  exact (pt_eq p F c hc).symm

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG
