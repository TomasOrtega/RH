import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfWaveQQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsCombineMk
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.TwistedTransfer

/- English proof (translation)
Unfold `fsv`. Rewrite using `[← Complex.exp_conj, ← Complex.exp_add]`. Use `Complex.exp_zero using 2` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub, map_mul, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fsv_mul_conj (s t : ℂ) : fsv s t * conj (fsv s t) = 1 := by
  unfold fsv
  rw [← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_sub, map_mul, Complex.conj_conj]
  ring

/- English proof (translation)
Simplify using `[fsv]`.
-/
theorem fsv_zero (t : ℂ) : fsv 0 t = 1 := by
  simp [fsv]

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

/- English proof (translation)
Establish `e : Formalism.FourierDecayAlt.B.hsVec (a • V) = a • Formalism.FourierDecayAlt.B.hsVec V`. Unfold `Formalism.FourierDecayAlt.B.hsVec`. Rewrite using `[← WithLp.toLp_smul]`. Both sides reduce to the same expression. Unfold `Formalism.FourierDecayAlt.B.hsInner`.

Rewrite using `[e, inner_smul_left]`.
-/
theorem hsInner_smul_right (a : ℂ) (U V : Wq →L[ℂ] Wp) : B.hsInner U (a • V) = conj a * B.hsInner U V := by
  have e : Formalism.FourierDecayAlt.B.hsVec (a • V) = a • Formalism.FourierDecayAlt.B.hsVec V := by
    unfold Formalism.FourierDecayAlt.B.hsVec
    rw [← WithLp.toLp_smul]
    rfl
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [e, inner_smul_left]

/- English proof (translation)
Unfold `pairAt`. Simplify using `only [hW Ψ c, hsInner_smul_right]`. Conclude with `integral_const_mul _ _`.
-/
theorem pairAt_mulOp_right (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Φ (Wv Ψ) c = conj (fsv s (c l)) * pairAt μ Φ Ψ c := by
  unfold pairAt
  simp only [hW Ψ c, hsInner_smul_right]
  exact integral_const_mul _ _

/- English proof (translation)
Unfold `form`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `c'`. Simplify using `only [act_io]`.

Express the relevant statement in the definitionally equal form `_ * ∑ a, pairAt μ (u a) (Wv (y a)) _ = _`. Simplify using `only [pairAt_mulOp_right μ l s Wv hW, glue_succ_update, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_mulOp_right (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ u (act (io (mkP Wv Wv')) y) (Function.update c l t) =
      conj (fsv s t) * form μ l.succ u y (Function.update c l t) := by
  unfold form
  rw [← integral_const_mul]
  congr 1
  funext c'
  simp only [act_io]
  change _ * ∑ a, pairAt μ (u a) (Wv (y a)) _ = _
  simp only [pairAt_mulOp_right μ l s Wv hW, glue_succ_update, ← Finset.mul_sum]
  ring

/- English proof (translation)
Establish `hU : ∀ w : List (Letter ℂ S), (UUiw (0 : ℂ) w : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) = 1`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons l w ih`.

Rewrite using `[UUiw, ih, mul_one]`. Establish `h0 : (Uinv (A` using `Pr (RadSp k r z z' π π')) (if l.plus then (0 : ℂ) else star 0)) = 1 := by`. Rewrite using `[star_zero, ite_self]`. Unfold `Uinv`. Rewrite using `[map_zero]`.

Conclude with `Matrix.one_fin_two.symm`. Rewrite using `[h0, Formalism.FourierDecayAlt.P.Wd11.liftMatrix_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]`. Establish `h1 : (mkP (1 : Module.End ℂ (RadSp k r z z' π π')) 1) = 1` using `rfl`. Use function extensionality and compare the values at `a`. Rewrite using `[Vw, hU, mul_one, h1, act_io]`.

Both sides reduce to the same expression.
-/
theorem act_Vw_zero (w : List (Letter ℂ S)) (x : Ix S → RadSp k r z z' π π') :
    act (Vw (mkP (1 : Module.End ℂ (RadSp k r z z' π π')) 1) 0 w) x = x := by
  have hU : ∀ w : List (Letter ℂ S), (UUiw (0 : ℂ) w : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) = 1 := by
    intro w
    induction w with
    | nil => rfl
    | cons l w ih =>
      rw [UUiw, ih, mul_one]
      have h0 : (Uinv (A := Pr (RadSp k r z z' π π')) (if l.plus then (0 : ℂ) else star 0)) = 1 := by
        rw [star_zero, ite_self]
        unfold Uinv
        rw [map_zero]
        exact Matrix.one_fin_two.symm
      rw [h0, Formalism.FourierDecayAlt.P.Wd11.liftMatrix_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]
  have h1 : (mkP (1 : Module.End ℂ (RadSp k r z z' π π')) 1) = 1 := rfl
  funext a
  rw [Vw, hU, mul_one, h1, act_io]
  rfl

/- English proof (translation)
Introduce `Φ c g`. Simplify using `[fsv_zero]`.
-/
theorem isMulOp_one_c (l : Fin r) :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun c _ => fsv 0 (c l)) := by
  intro Φ c g
  simp [fsv_zero]

/- English proof (translation)
Introduce `Φ c g`. Simplify using `[fsv_zero]`.
-/
theorem isMulOp_one_c' (l : Fin r) :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun c _ => fsv (-0) (c l)) := by
  intro Φ c g
  simp [fsv_zero]

/- English proof (translation)
Introduce `Φ c g`. Simplify using `[fsv_zero]`.
-/
theorem isMulOp_one_zeta :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun _ g => fsv 0 (P5.zeta k r z z' g)) := by
  intro Φ c g
  simp [fsv_zero]

/- English proof (translation)
Introduce `Φ c g`. Simplify using `[fsv_zero]`.
-/
theorem isMulOp_one_zeta_conj :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun _ g => fsv (-0) (P5.zeta k r z z' g)) := by
  intro Φ c g
  simp [fsv_zero]

end Wave

section Step

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)

/- English proof (translation)
Take `⟨hwave, hc1, hc2, hp⟩` from `waveSiteAll Wp Wq P z z' π π' X L hD.2.2.1 l s Wv Wv' hW hW'`. Establish `hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w` using `Formalism.FourierDecayAlt.P.plane_wave_vector_identity ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hnd`. Simplify using `only [P5.ph, RRform]`. Rewrite using `[← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) y, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) y, form_mulOp_right μ l s Wv Wv' hW]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ph_wave_right (hD : IsData P z z' π π' X μ L st l0) (w : List (Letter ℂ S))
    (hnd : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (l : Fin P.r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (t : ℂ) :
    ph L st μ l w x (act (Vw (mkP Wv Wv') s w) y) c t = conj (fsv s t) * ph L st μ l w x y c t := by
  obtain ⟨hwave, hc1, hc2, hp⟩ := waveSiteAll Wp Wq P z z' π π' X L hD.2.2.1 l s Wv Wv' hW hW'
  have hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w :=
    Formalism.FourierDecayAlt.P.plane_wave_vector_identity ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hnd
  simp only [P5.ph, RRform]
  rw [← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) y, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) y,
    form_mulOp_right μ l s Wv Wv' hW]
  ring

/- English proof (translation)
Establish `hl : (⟨0, hr⟩ : Fin P.r).castSucc = 0` using `Fin.ext rfl`. Establish `hstep` using `(hOn w hw).2.1 ⟨0, hr⟩`. Unfold `StepP at hstep`. Rewrite `hstep` using `[hl]`. Take `⟨φ, -, hφ, -, hφs⟩` from `hstep x (act (Vw (mkP Wv Wv') s w) y) hx hVy c hc`.

Take `⟨ψ, -, hψ, -, hψs⟩` from `hstep x y hx hy c hc`. Establish `h1` using `hφs s Wv Wv' hW hW'`. Establish `h0` using `hψs 0 1 1 (isMulOp_one_c _) (isMulOp_one_c' _)`. Rewrite `h0` using `[act_Vw_zero]`. Rewrite using `[← h1, ← h0]`.

Establish `hae : ∀ᵐ t : ℂ ∂volume, t ≠ 0`. Rewrite using `[ae_iff]`. Simplify using `using (measure_singleton (0 : ℂ) : volume ({0} : Set ℂ) = 0)`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with t ht`.

Rewrite using `[hφ t ht, hψ t ht, ph_wave_right P z z' π π' X μ L st l0 hD w hw.1.1 ⟨0, hr⟩ s Wv Wv' hW hW', fsv_zero, ← mul_assoc, fsv_mul_conj, one_mul]`.
-/
theorem rr_wave_A (hD : IsData P z z' π π' X μ L st l0) (hOn : ThmPOn (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (hr : 0 < P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c ⟨0, hr⟩))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c ⟨0, hr⟩)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K 0) x) (hy : InK (K 0) y)
    (hVy : InK (K 0) (act (Vw (mkP Wv Wv') s w) y)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) :
    RRform L st μ 0 w (act (Vw (mkP Wv Wv') s w) x) (act (Vw (mkP Wv Wv') s w) y) c = RRform L st μ 0 w x y c := by
  have hl : (⟨0, hr⟩ : Fin P.r).castSucc = 0 := Fin.ext rfl
  have hstep := (hOn w hw).2.1 ⟨0, hr⟩
  unfold StepP at hstep
  rw [hl] at hstep
  obtain ⟨φ, -, hφ, -, hφs⟩ := hstep x (act (Vw (mkP Wv Wv') s w) y) hx hVy c hc
  obtain ⟨ψ, -, hψ, -, hψs⟩ := hstep x y hx hy c hc
  have h1 := hφs s Wv Wv' hW hW'
  have h0 := hψs 0 1 1 (isMulOp_one_c _) (isMulOp_one_c' _)
  rw [act_Vw_zero] at h0
  rw [← h1, ← h0]
  have hae : ∀ᵐ t : ℂ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℂ) : volume ({0} : Set ℂ) = 0)
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [hφ t ht, hψ t ht, ph_wave_right P z z' π π' X μ L st l0 hD w hw.1.1 ⟨0, hr⟩ s Wv Wv' hW hW',
    fsv_zero, ← mul_assoc, fsv_mul_conj, one_mul]

/- English proof (translation)
Take `⟨hP, -, hAL, hQQ, -, -, hSL, hLS⟩` from `hD`. Establish `hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = fsv s (P5.zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g` using `hW`. Establish `hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = fsv (-s) (P5.zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g` using `hW'`. Establish `hWW' : Wv * Wv' = 1`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `Φ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c g`. Simplify using `only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]`. Establish `hW'W : Wv' * Wv = 1`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `Φ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c g`. Simplify using `only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]`.

Establish `f_fi : mkP Wv Wv' * mkP Wv' Wv = 1` using `pr_ext (by simpa using hWW') (by simpa using hWW')`. Establish `fi_f : mkP Wv' Wv * mkP Wv Wv' = 1` using `pr_ext (by simpa using hW'W) (by simpa using hW'W)`. Establish `hfn : ∀ g ∈ Fr.zfns L, Commute (mkP Wv Wv') g`. Take `⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hG, hGi, -⟩` from `hAL`. Establish `key : ∀ j j' : Fin 6, Commute (mkP Wv Wv') (mkP (X.fn j) (X.fn j'))`.

Introduce `j j'`. Use `show _ * _ = _ * _`. Conclude with `pr_ext (by simpa using mulOp_comm_fn X Wv _ hW j) (by simpa using (mulOp_comm_fn X Wv' _ hW' j').symm)`. Introduce `g hg`. Simplify using `only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg`.

Break down `hg with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Rewrite using `[hz]`. Conclude with `key _ _`. Rewrite using `[hzi]`. Conclude with `key _ _`.

Rewrite using `[hzb]`. Conclude with `key _ _`. Rewrite using `[hzbi]`. Conclude with `key _ _`. Rewrite using `[hG]`.

Conclude with `key _ _`. Rewrite using `[hGi]`. Conclude with `key _ _`. Establish `hGG : Commute (mkP Wv Wv') L.GG` using `hfn _ (mem_zfns L).2.2.2.2.1`. Establish `hfiGG : Commute (mkP Wv' Wv) L.GG` using `(commute_inv hGG.symm f_fi fi_f).symm`.

Take `⟨e11, e10⟩` from `zeta_entries Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt hP X st l0 hQQ s Wv Wv' hW hW'`. Establish `hx : ∀ Y, Commute (mkP Wv Wv') (st.x Y)`. Introduce `Y`. Establish `h` using `e11 Y`. Rewrite `h` using `[hLS.tau Y]`.

Establish `h1 : L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv') = L.GG * st.x Y` using `by conv_rhs => rw [← h]`. Rewrite using `[← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq]`. Simplify using `only [mul_assoc]`. Establish `h2 : mkP Wv' Wv * st.x Y * mkP Wv Wv' = st.x Y`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, L.GGi_GG, one_mul]`. Use `_ = L.GGi * (L.GG * st.x Y) := by rw [h1]`. Use `_ = st.x Y := by rw [← mul_assoc, L.GGi_GG, one_mul]`. Use `show mkP Wv Wv' * st.x Y = st.x Y * mkP Wv Wv'`. Combine the equalities or inequalities in the displayed calculation.

Establish `hl : ∀ Y ∈ st.inv, mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv' = L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ _ s`. Introduce `Y hY`. Establish `h` using `e10 Y`. Rewrite `h` using `[hLS.low Y hY, hLS.tau Y]`. Establish `hfix : Commute (mkP Wv' Wv) (st.x Y)` using `(commute_inv (hx Y).symm f_fi fi_f).symm`.

Establish `cancel : ∀ T, st.xi Y * L.GGi * (L.GG * st.x Y * T) = T`. Introduce `T`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = T := by rw [L.GGi_GG, mul_one, (hLS.x_xi Y hY).2, one_mul]`.

Establish `h3 : mkP Wv' Wv * (L.GG * st.x Y * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)) * mkP Wv Wv' = L.GG * st.x Y * (mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv')`. Rewrite using `[← mul_assoc (mkP Wv' Wv) (L.GG * st.x Y), ← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq, mul_assoc L.GG (mkP Wv' Wv), hfix.eq]`. Simplify using `only [mul_assoc]`. Rewrite `h` using `[h3, ← mul_sub]`. Rewrite using `[← cancel (mkP Wv' Wv * _ * mkP Wv Wv'), h, cancel]`.

Establish `hWH : WaveHyp L st (mkP Wv Wv') (mkP Wv' Wv) s` using `⟨f_fi, fi_f, rfl, hfn, hx, hl⟩`. Take `⟨hFV, -⟩` from `frame_twist_F hSL hLS hWH w hw`. Unfold `topDens`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations.

Rewrite using `[← act_mul, hFV, act_mul (io (mkP Wv Wv')) (Fr.ofWord L st w).F y, act_io, mkPair_fst', hW1, hsInner_smul_right]`.
-/
theorem topDens_wave_right (hD : IsData P z z' π π' X μ L st l0) (w : List (Letter ℂ S))
    (hw : Fr.admitted st w) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun _ g => fsv s (P5.zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (P5.zeta P.k P.r z z' g)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r) :
    topDens L st w x (act (Vw (mkP Wv Wv') s w) y) c g =
      conj (fsv s (P5.zeta P.k P.r z z' g)) * topDens L st w x y c g := by
  obtain ⟨hP, -, hAL, hQQ, -, -, hSL, hLS⟩ := hD
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (P5.zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (P5.zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]
  have f_fi : mkP Wv Wv' * mkP Wv' Wv = 1 := pr_ext (by simpa using hWW') (by simpa using hWW')
  have fi_f : mkP Wv' Wv * mkP Wv Wv' = 1 := pr_ext (by simpa using hW'W) (by simpa using hW'W)
  have hfn : ∀ g ∈ Fr.zfns L, Commute (mkP Wv Wv') g := by
    obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hAL
    have key : ∀ j j' : Fin 6, Commute (mkP Wv Wv') (mkP (X.fn j) (X.fn j')) := by
      intro j j'
      show _ * _ = _ * _
      exact pr_ext (by simpa using mulOp_comm_fn X Wv _ hW j) (by simpa using (mulOp_comm_fn X Wv' _ hW' j').symm)
    intro g hg
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact key _ _
    · rw [hzi]; exact key _ _
    · rw [hzb]; exact key _ _
    · rw [hzbi]; exact key _ _
    · rw [hG]; exact key _ _
    · rw [hGi]; exact key _ _
  have hGG : Commute (mkP Wv Wv') L.GG := hfn _ (mem_zfns L).2.2.2.2.1
  have hfiGG : Commute (mkP Wv' Wv) L.GG := (commute_inv hGG.symm f_fi fi_f).symm
  obtain ⟨e11, e10⟩ := zeta_entries Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt hP X st l0 hQQ s Wv Wv' hW hW'
  have hx : ∀ Y, Commute (mkP Wv Wv') (st.x Y) := by
    intro Y
    have h := e11 Y
    rw [hLS.tau Y] at h
    have h1 : L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv') = L.GG * st.x Y := by
      conv_rhs => rw [← h]
      rw [← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq]
      simp only [mul_assoc]
    have h2 : mkP Wv' Wv * st.x Y * mkP Wv Wv' = st.x Y := by
      calc mkP Wv' Wv * st.x Y * mkP Wv Wv' = L.GGi * (L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv')) := by
            rw [← mul_assoc, L.GGi_GG, one_mul]
        _ = L.GGi * (L.GG * st.x Y) := by rw [h1]
        _ = st.x Y := by rw [← mul_assoc, L.GGi_GG, one_mul]
    show mkP Wv Wv' * st.x Y = st.x Y * mkP Wv Wv'
    calc mkP Wv Wv' * st.x Y = mkP Wv Wv' * (mkP Wv' Wv * st.x Y * mkP Wv Wv') := by rw [h2]
      _ = st.x Y * mkP Wv Wv' := by rw [← mul_assoc, ← mul_assoc, f_fi, one_mul]
  have hl : ∀ Y ∈ st.inv, mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv' =
      L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ _ s := by
    intro Y hY
    have h := e10 Y
    rw [hLS.low Y hY, hLS.tau Y] at h
    have hfix : Commute (mkP Wv' Wv) (st.x Y) := (commute_inv (hx Y).symm f_fi fi_f).symm
    have cancel : ∀ T, st.xi Y * L.GGi * (L.GG * st.x Y * T) = T := by
      intro T
      calc st.xi Y * L.GGi * (L.GG * st.x Y * T) = st.xi Y * (L.GGi * L.GG) * st.x Y * T := by
            simp only [mul_assoc]
        _ = T := by rw [L.GGi_GG, mul_one, (hLS.x_xi Y hY).2, one_mul]
    have h3 : mkP Wv' Wv * (L.GG * st.x Y * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)) * mkP Wv Wv' =
        L.GG * st.x Y * (mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv') := by
      rw [← mul_assoc (mkP Wv' Wv) (L.GG * st.x Y), ← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq,
        mul_assoc L.GG (mkP Wv' Wv), hfix.eq]
      simp only [mul_assoc]
    rw [h3, ← mul_sub] at h
    rw [← cancel (mkP Wv' Wv * _ * mkP Wv Wv'), h, cancel]
  have hWH : WaveHyp L st (mkP Wv Wv') (mkP Wv' Wv) s := ⟨f_fi, fi_f, rfl, hfn, hx, hl⟩
  obtain ⟨hFV, -⟩ := frame_twist_F hSL hLS hWH w hw
  unfold topDens
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← act_mul, hFV, act_mul (io (mkP Wv Wv')) (Fr.ofWord L st w).F y, act_io, mkPair_fst', hW1, hsInner_smul_right]

/- English proof (translation)
Establish `hl : (0 : Fin (P.r + 1)) = Fin.last P.r` using `Fin.ext (by simp [hr])`. Take `⟨hTop, -, -⟩` from `hOn w hw`. Rewrite `hx`, `hy`, `hVy`, the goal using `[hl]`. Take `⟨-, hφs, -⟩` from `hTop x (act (Vw (mkP Wv Wv') s w) y) hx hVy c hc`. Take `⟨-, hψs, -⟩` from `hTop x y hx hy c hc`.

Establish `h0` using `hψs 0 1 1 isMulOp_one_zeta isMulOp_one_zeta_conj`. Rewrite `h0` using `[act_Vw_zero]`. Rewrite using `[← hφs s Wv Wv' hW hW', ← h0]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Rewrite using `[topDens_wave_right P z z' π π' X μ L st l0 hD w hw.1 s Wv Wv' hW hW', fsv_zero, ← mul_assoc, fsv_mul_conj, one_mul]`.
-/
theorem rr_wave_B (hD : IsData P z z' π π' X μ L st l0) (hOn : ThmPOn (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (hr : P.r = 0) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun _ g => fsv s (P5.zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (P5.zeta P.k P.r z z' g)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K 0) x) (hy : InK (K 0) y)
    (hVy : InK (K 0) (act (Vw (mkP Wv Wv') s w) y)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) :
    RRform L st μ 0 w (act (Vw (mkP Wv Wv') s w) x) (act (Vw (mkP Wv Wv') s w) y) c = RRform L st μ 0 w x y c := by
  have hl : (0 : Fin (P.r + 1)) = Fin.last P.r := Fin.ext (by simp [hr])
  obtain ⟨hTop, -, -⟩ := hOn w hw
  rw [hl] at hx hy hVy ⊢
  obtain ⟨-, hφs, -⟩ := hTop x (act (Vw (mkP Wv Wv') s w) y) hx hVy c hc
  obtain ⟨-, hψs, -⟩ := hTop x y hx hy c hc
  have h0 := hψs 0 1 1 isMulOp_one_zeta isMulOp_one_zeta_conj
  rw [act_Vw_zero] at h0
  rw [← hφs s Wv Wv' hW hW', ← h0]
  congr 1
  funext g
  rw [topDens_wave_right P z z' π π' X μ L st l0 hD w hw.1 s Wv Wv' hW hW', fsv_zero, ← mul_assoc, fsv_mul_conj,
    one_mul]

end Step

end Formalism.FourierDecayAlt.P.PBFV
