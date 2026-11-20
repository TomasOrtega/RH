import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDM

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

/- English proof (translation)
Unfold `TBB.nPt D.ptGG`. Rewrite using `[Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt]`. Conclude with `Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights k r _ (r + 1) c 1`.
-/
theorem nPt_bigPt_eq (k r : ℕ) (TT : ℝ) (c : Fin (r + 1) → ℂ) :
    TBB.nPt k r TT (TBB.bigPt r c) = ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then
      (Complex.normSq (c (Fin.last r)) - TT) ^ (k - 1)
      else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
  unfold TBB.nPt D.ptGG
  rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt]
  exact Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights k r _ (r + 1) c 1

/- English proof (translation)
Simplify using `only [nPt_bigPt_eq]`. Use `Finset.measurable_prod _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : 1 + (i : ℕ) = r + 1`. Simplify using `only [h, if_true]`. Conclude with `((Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)).sub_const _).pow_const _`.

Simplify using `only [h, if_false]`. Establish `hm : Measurable (fun c : Fin (r + 1) → ℂ => ‖c i‖)` using `continuous_norm.measurable.comp (measurable_pi_apply i)`. Conclude with `hm.pow_const _`.
-/
theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) := by
  simp only [nPt_bigPt_eq]
  refine Finset.measurable_prod _ fun i _ => ?_
  by_cases h : 1 + (i : ℕ) = r + 1
  · simp only [h, if_true]
    exact ((Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)).sub_const _).pow_const _
  · simp only [h, if_false]
    have hm : Measurable (fun c : Fin (r + 1) → ℂ => ‖c i‖) := continuous_norm.measurable.comp (measurable_pi_apply i)
    exact hm.pow_const _

/- English proof (translation)
Use `show Complex.normSq (D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (r + 1)).det / D.ptG TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _`. Unfold `D.ptG`. Rewrite using `[Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal]`.
-/
theorem wPt_bigPt_eq (TT : ℝ) (r : ℕ) (c : Fin (r + 1) → ℂ) :
    Top.wPt TT r (TBB.bigPt r c) = Complex.normSq (∏ i, c i) /
      (Complex.normSq (∏ i, c i) - TT * Complex.normSq (∏ a : Fin r, c a.castSucc)) := by
  show Complex.normSq (D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (r + 1)).det /
    D.ptG TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
  unfold D.ptG
  rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
    Matrix.det_diagonal, Matrix.det_diagonal]

/- English proof (translation)
Simplify using `only [wPt_bigPt_eq]`. Establish `h1 : Measurable (fun c : Fin (r + 1) → ℂ => Complex.normSq (∏ i, c i))` using `(Complex.continuous_normSq.comp (continuous_finsetProd _ fun i _ => continuous_apply i)).measurable`. Establish `h2 : Measurable (fun c : Fin (r + 1) → ℂ => Complex.normSq (∏ a : Fin r, c a.castSucc))` using `(Complex.continuous_normSq.comp (continuous_finsetProd _ fun a _ => continuous_apply _)).measurable`. Conclude with `h1.div (h1.sub (h2.const_mul TT))`.
-/
theorem measurable_wPt_bigPt (TT : ℝ) (r : ℕ) :
    Measurable (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) := by
  simp only [wPt_bigPt_eq]
  have h1 : Measurable (fun c : Fin (r + 1) → ℂ => Complex.normSq (∏ i, c i)) :=
    (Complex.continuous_normSq.comp (continuous_finsetProd _ fun i _ => continuous_apply i)).measurable
  have h2 : Measurable (fun c : Fin (r + 1) → ℂ => Complex.normSq (∏ a : Fin r, c a.castSucc)) :=
    (Complex.continuous_normSq.comp (continuous_finsetProd _ fun a _ => continuous_apply _)).measurable
  exact h1.div (h1.sub (h2.const_mul TT))

/- English proof (translation)
Introduce `k r TT` and use `⟨measurable_nPt_bigPt k r TT, measurable_wPt_bigPt TT r⟩`.
-/
theorem scalar_point_measurability_holds : ScalarMeas := fun k r TT => ⟨measurable_nPt_bigPt k r TT, measurable_wPt_bigPt TT r⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Unfold `B.gN`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (g i j)), Complex.sq_norm]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Establish `h1 : Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j')` using `Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ j)`. Establish `h2 : ∑ j', Complex.normSq (g i j') ≤ ∑ i', ∑ j', Complex.normSq (g i' j')` using `Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j')) (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)`.

Conclude with `h1.trans h2`.
-/
theorem entry_le_gN {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  rw [← Real.sqrt_sq (norm_nonneg (g i j)), Complex.sq_norm]
  apply Real.sqrt_le_sqrt
  have h1 : Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
    Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun j' _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', Complex.normSq (g i j') ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
    Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
      (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

/- English proof (translation)
Establish `hc : Continuous (fun g : B.Mat k r => B.gN g)`. Unfold `B.gN`. Conclude with `Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))`. Use `Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_` and prove the remaining obligations. Rewrite using `[isBounded_iff_forall_norm_le]`.

Use `⟨max R 0, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.norm_le_iff (le_max_right _ _)]`. Introduce `i j`. Conclude with `(entry_le_gN g i j).trans (le_trans hg (le_max_left _ _))`.
-/
theorem gN_ball_compact (k r : ℕ) (R : ℝ) : IsCompact {g : B.Mat k r | B.gN g ≤ R} := by
  have hc : Continuous (fun g : B.Mat k r => B.gN g) := by
    unfold B.gN
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max R 0, fun g hg => ?_⟩
  rw [Matrix.norm_le_iff (le_max_right _ _)]
  intro i j
  exact (entry_le_gN g i j).trans (le_trans hg (le_max_left _ _))

/- English proof (translation)
Take `⟨R, hR⟩` from `hX.2.1`. Conclude with `Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hX.1 (gN_ball_compact k r R) (fun g hg hgC => by by_contra h; exact hgC (hR g hg h)) A m`.
-/
theorem cptCoef_inCC {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {X : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hX : KB.CptCoef Bs X) (A : ℝ) (m : ℕ) : B.InCC A m X := by
  obtain ⟨R, hR⟩ := hX.2.1
  exact Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hX.1 (gN_ball_compact k r R)
    (fun g hg hgC => by by_contra h; exact hgC (hR g hg h)) A m

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p X hX`. Use `set Bs := p.T.base with hBs`. Use `set T := Tz P.k P.r Bs.z with hT`. Use `set T' := Tz P.k P.r Bs.z' with hT'`. Use `set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA`.

Establish `hThr : JF.TransportedAlt P.k P.r A 0`. Unfold `JF.TransportedAlt`. Establish `hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1)` using `by positivity`. Rewrite using `[Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hc` using `Formalism.FourierDecayAlt.P.CutBP.jgq_continuousOn Bs hThr (cptCoef_inCC Bs hX A 0)`. Establish `hcn : ContinuousOn (fun q => ‖B.hsVec (B.JF Bs X (B.gq Bs q))‖ ^ 2) (JF.QDom P.k P.r Bs.z Bs.z')` using `((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.continuous.comp_continuousOn hc).norm).pow 2`. Establish `hm` using `Formalism.FourierDecayAlt.P.CutBP.aesm_weight_smul Bs hcn`. Set `e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ` to `(MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm`. Establish `hmp : MeasurePreserving e volume volume` using `(Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))`.

Establish `he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r))`. Introduce `c`. Simplify using `[e, MeasurableEquiv.piFinSuccAbove]`. Both sides reduce to the same expression. Establish `hm2` using `hm.comp_measurePreserving hmp`.

Use `hm2.congr ?_` and prove the remaining obligations. Use `filter_upwards [ae_all_ne P.r] with c hc0`. Use `show bcWeight P.k P.r T T' (e c) • ‖B.hsVec (B.JF Bs X (B.gq Bs (e c)))‖ ^ 2 = topD p X [] c`. Rewrite using `[he c, smul_eq_mul]`. Establish `hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)` using `Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc0`.

Unfold `topD`. Rewrite using `[Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p X hl]`. Establish `hk : 2 ≤ P.k` using `p.hl.2.2`. Establish `hcin : ∀ a : Fin P.r, c a.castSucc ≠ 0` using `fun a => hc0 _`. Establish `hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc)` using `Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hcin a)`.

Establish `hGeq : TBB.Gp p (TBB.bigPt P.r c) = Complex.normSq (∏ i : Fin P.r, c i.castSucc) * (Complex.normSq (c (Fin.last P.r)) - T * T')` using `by show D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _`. Unfold `D.ptG`. Rewrite using `[Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hG : 0 < TBB.Gp p (TBB.bigPt P.r c)`.

Rewrite using `[Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p X c hc0 hG]`. Establish `hζ : T * T' ≤ Complex.normSq (c (Fin.last P.r))`. Rewrite `hG` using `[hGeq]`. Use `(pos_iff_pos_of_mul_pos hG).1 hp` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r))` using `Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r T T' c hζ`. Rewrite using `[hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]`. Both sides reduce to the same expression. Establish `hV : p.V X (TBB.bigPt P.r c) = 0`. Unfold `KB.Pl.V D.vecV`.

Rewrite using `[dif_neg (fun h => hG h.2)]`. Rewrite using `[hV]`. Establish `hw0 : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0`. Unfold `bcWeight`. Use `split_ifs with hle`.

Establish `hle2 : Complex.normSq (c (Fin.last P.r)) ≤ T * T'`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Apply `hG` to reduce the goal to its premises. Rewrite using `[hGeq]`.

Conclude with `mul_pos hp (by linarith)`. Establish `hle' : T * T' ≤ Complex.normSq (c (Fin.last P.r))` using `hle`. Establish `heq : Complex.normSq (c (Fin.last P.r)) - T * T' = 0` using `by linarith`. Use `show (∏ a : Fin P.r, ‖c a.castSucc‖ ^ (2 * (Mdim P.k P.r a - 2))) * (Complex.normSq (c (Fin.last P.r)) - T * T') ^ (P.k - 1) = 0`. Rewrite using `[heq, zero_pow (by omega), mul_zero]`.

Both sides reduce to the same expression. Rewrite using `[hw0]`. Establish `h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0`. Unfold `B.hsVec`. Both sides reduce to the same expression.

Simplify using `[h0]`.
-/
theorem empty_list_measurability_holds : EmptyMeas := by
  intro Wp Wq _ _ _ _ _ _ P p X hX
  set Bs := p.T.base with hBs
  set T := Tz P.k P.r Bs.z with hT
  set T' := Tz P.k P.r Bs.z' with hT'
  set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA
  have hThr : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    have hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]
    nlinarith
  have hc := Formalism.FourierDecayAlt.P.CutBP.jgq_continuousOn Bs hThr (cptCoef_inCC Bs hX A 0)
  have hcn : ContinuousOn (fun q => ‖B.hsVec (B.JF Bs X (B.gq Bs q))‖ ^ 2) (JF.QDom P.k P.r Bs.z Bs.z') :=
    ((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.continuous.comp_continuousOn hc).norm).pow 2
  have hm := Formalism.FourierDecayAlt.P.CutBP.aesm_weight_smul Bs hcn
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  have hm2 := hm.comp_measurePreserving hmp
  refine hm2.congr ?_
  filter_upwards [ae_all_ne P.r] with c hc0
  show bcWeight P.k P.r T T' (e c) • ‖B.hsVec (B.JF Bs X (B.gq Bs (e c)))‖ ^ 2 = topD p X [] c
  rw [he c, smul_eq_mul]
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc0
  unfold topD
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p X hl]
  have hk : 2 ≤ P.k := p.hl.2.2
  have hcin : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hc0 _
  have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hcin a)
  have hGeq : TBB.Gp p (TBB.bigPt P.r c) =
      Complex.normSq (∏ i : Fin P.r, c i.castSucc) * (Complex.normSq (c (Fin.last P.r)) - T * T') := by
    show D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    ring
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · rw [Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p X c hc0 hG]
    have hζ : T * T' ≤ Complex.normSq (c (Fin.last P.r)) := by
      rw [hGeq] at hG
      have := (pos_iff_pos_of_mul_pos hG).1 hp
      linarith
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r T T' c hζ
    rw [hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]
    rfl
  · have hV : p.V X (TBB.bigPt P.r c) = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dif_neg (fun h => hG h.2)]
    rw [hV]
    have hw0 : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0 := by
      unfold bcWeight
      split_ifs with hle
      · have hle2 : Complex.normSq (c (Fin.last P.r)) ≤ T * T' := by
          by_contra hlt
          push Not at hlt
          apply hG
          rw [hGeq]
          exact mul_pos hp (by linarith)
        have hle' : T * T' ≤ Complex.normSq (c (Fin.last P.r)) := hle
        have heq : Complex.normSq (c (Fin.last P.r)) - T * T' = 0 := by linarith
        show (∏ a : Fin P.r, ‖c a.castSucc‖ ^ (2 * (Mdim P.k P.r a - 2))) *
          (Complex.normSq (c (Fin.last P.r)) - T * T') ^ (P.k - 1) = 0
        rw [heq, zero_pow (by omega), mul_zero]
      · rfl
    rw [hw0]
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      rfl
    simp [h0]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
