import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableBlockIntegrand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.YGSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCongrRight

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory Filter

noncomputable section

/- English proof (translation)
Set `bo : ContDiffBump (0 : ℂ)` to `⟨r₂, 2 * r₂, by linarith, by linarith⟩`. Set `bi : ContDiffBump (0 : ℂ)` to `⟨r₁ / 4, r₁ / 2, by linarith, by linarith⟩`. Establish `hsupp : tsupport (fun w : ℂ => (((1 - bi w) * bo w : ℝ) : ℂ)) ⊆ Metric.closedBall 0 (2 * r₂)`. Use `(tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero _).trans ?_` and prove the remaining obligations. Use `(tsupport_mul_subset_right).trans ?_` and prove the remaining obligations.

Rewrite using `[bo.tsupport_eq]`. Use `⟨fun w => (((1 - bi w) * bo w : ℝ) : ℂ), ⟨?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Complex.ofRealCLM.contDiff.comp ((contDiff_const.sub bi.contDiff).mul bo.contDiff)`. Establish `h` using `(bo.hasCompactSupport.mul_left (f := fun w : ℂ => 1 - bi w)).comp_left Complex.ofReal_zero`. Conclude with `h`.

Introduce `h0`. Establish `hnb : ∀ᶠ w in nhds (0 : ℂ), (((1 - bi w) * bo w : ℝ) : ℂ) = 0` using `by filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by linarith : (0 : ℝ) < r₁ / 4)] with w hw`. Establish `: bi w = 1` using `bi.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)`. Simplify using `[this]`. Conclude with `(notMem_tsupport_iff_eventuallyEq.2 hnb) h0`.

Introduce `w hw1 hw2`. Establish `ho : bo w = 1` using `bo.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hw2)`. Establish `hi : bi w = 0` using `bi.zero_of_le_dist (by show r₁ / 2 ≤ dist w 0`. Rewrite using `[dist_zero_right]`. Use the proof step `linarith)`.

Simplify using `[ho, hi]`. Introduce `w hw`. Use `hsupp hw` as an intermediate fact. Simplify `this` using `[Metric.mem_closedBall, dist_zero_right]`.
-/
theorem bump_annulus {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h12 : r₁ ≤ r₂) :
    ∃ χD : ℂ → ℂ, U.IsCutC χD ∧ (∀ w : ℂ, r₁ ≤ ‖w‖ → ‖w‖ ≤ r₂ → χD w = 1) ∧
      (∀ w ∈ tsupport χD, ‖w‖ ≤ 2 * r₂) := by
  let bo : ContDiffBump (0 : ℂ) := ⟨r₂, 2 * r₂, by linarith, by linarith⟩
  let bi : ContDiffBump (0 : ℂ) := ⟨r₁ / 4, r₁ / 2, by linarith, by linarith⟩
  have hsupp : tsupport (fun w : ℂ => (((1 - bi w) * bo w : ℝ) : ℂ)) ⊆ Metric.closedBall 0 (2 * r₂) := by
    refine (tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero _).trans ?_
    refine (tsupport_mul_subset_right).trans ?_
    rw [bo.tsupport_eq]
  refine ⟨fun w => (((1 - bi w) * bo w : ℝ) : ℂ), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.sub bi.contDiff).mul bo.contDiff)
  · have h := (bo.hasCompactSupport.mul_left (f := fun w : ℂ => 1 - bi w)).comp_left Complex.ofReal_zero
    exact h
  · intro h0
    have hnb : ∀ᶠ w in nhds (0 : ℂ), (((1 - bi w) * bo w : ℝ) : ℂ) = 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by linarith : (0 : ℝ) < r₁ / 4)] with w hw
      have : bi w = 1 := bi.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
      simp [this]
    exact (notMem_tsupport_iff_eventuallyEq.2 hnb) h0
  · intro w hw1 hw2
    have ho : bo w = 1 := bo.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hw2)
    have hi : bi w = 0 := bi.zero_of_le_dist (by
      show r₁ / 2 ≤ dist w 0
      rw [dist_zero_right]; linarith)
    simp [ho, hi]
  · intro w hw
    have := hsupp hw
    simpa [Metric.mem_closedBall, dist_zero_right] using this

/- English proof (translation)
Use `⟨?_, ptSize_ptG h' m q⟩` and prove the remaining obligations. Break down `q with ⟨t, c⟩ | z` into its components or cases. Take `⟨ht, hc⟩` from `hq`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hc`. Conclude with `hK0 hc`. Introduce `b hb`. Simplify using `only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb`. Break down `hb with hb | rfl | rfl` into its components or cases.

Conclude with `hh'.1 b hb`. Conclude with `⟨by omega, ht⟩`. Conclude with `⟨le_rfl, hc0⟩`. Take `⟨D, hD, hz⟩` from `hq`. Establish `hz0 : z ≠ 0`.

Introduce and unpack `rfl`. Establish `h0 : ((-1 : ℂ) ^ (m + 3)) * D = 0` using `by rw [← hz]; simp`. Establish `: D = 0` using `(mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (by norm_num))`. Conclude with `hK0 (this ▸ hD)`. Introduce `b hb`.

Simplify using `only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb`. Break down `hb with hb | rfl` into its components or cases. Conclude with `hh'.1 b hb`. Conclude with `⟨by omega, hz0⟩`.
-/
theorem isLocPt_ptG {h' : C.LPt} (hh' : D.IsLocPt h' (D.ptSize h')) {m : ℕ} {Kc : Set ℂ} (hK0 : (0 : ℂ) ∉ Kc)
    {q : (ℂ × ℂ) ⊕ ℂ} (hq : okG m Kc q) : D.IsLocPt (ptG h' m q) (D.ptSize h' + (m + 2)) := by
  refine ⟨?_, ptSize_ptG h' m q⟩
  rcases q with ⟨t, c⟩ | z
  · obtain ⟨ht, hc⟩ := hq
    have hc0 : c ≠ 0 := by
      rintro rfl; simp at hc; exact hK0 hc
    intro b hb
    simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | rfl | rfl
    · exact hh'.1 b hb
    · exact ⟨by omega, ht⟩
    · exact ⟨le_rfl, hc0⟩
  · obtain ⟨D, hD, hz⟩ := hq
    have hz0 : z ≠ 0 := by
      rintro rfl
      have h0 : ((-1 : ℂ) ^ (m + 3)) * D = 0 := by rw [← hz]; simp
      have : D = 0 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (by norm_num))
      exact hK0 (this ▸ hD)
    intro b hb
    simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | rfl
    · exact hh'.1 b hb
    · exact ⟨by omega, hz0⟩

/- English proof (translation)
Establish `hR1 : 1 ≤ RR` using `by linarith`. Establish `h1 : (m + 1) * (m + 4) < (m + 3) ^ 2` using `by nlinarith`. Establish `h2 : (m + 3) ^ 2 ≤ RR ^ 2` using `pow_le_pow_left₀ (by linarith) hR 2`. Establish `h3 : RR ^ 2 ≤ RR ^ 3` using `pow_le_pow_right₀ hR1 (by norm_num)`. Establish `h4 : RR ^ 3 ≤ 128 * RR ^ 3 * As`.

Establish `: 0 ≤ RR ^ 3` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem arith_ma (m RR As a : ℝ) (hm : 0 ≤ m) (hR : m + 3 ≤ RR) (hAs : 1 ≤ As)
    (ha : 128 * RR ^ 3 * As ≤ a) : (m + 1) * (m + 4) < a := by
  have hR1 : 1 ≤ RR := by linarith
  have h1 : (m + 1) * (m + 4) < (m + 3) ^ 2 := by nlinarith
  have h2 : (m + 3) ^ 2 ≤ RR ^ 2 := pow_le_pow_left₀ (by linarith) hR 2
  have h3 : RR ^ 2 ≤ RR ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have h4 : RR ^ 3 ≤ 128 * RR ^ 3 * As := by
    have : 0 ≤ RR ^ 3 := by positivity
    nlinarith
  linarith

/- English proof (translation)
Establish `hR3 : 1 ≤ RR ^ 3` using `one_le_pow₀ hR1`. Establish `h1 : 128 * RR ^ 3 * (11 * X + 5) ≤ 128 * RR ^ 3 * As` using `mul_le_mul_of_nonneg_left hX (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem arith_auser (RR As X a : ℝ) (hR1 : 1 ≤ RR) (hX0 : 0 ≤ X) (hX : 11 * X + 5 ≤ As)
    (ha : 128 * RR ^ 3 * As ≤ a) : 127 * RR ^ 3 * X + 1 ≤ a := by
  have hR3 : 1 ≤ RR ^ 3 := one_le_pow₀ hR1
  have h1 : 128 * RR ^ 3 * (11 * X + 5) ≤ 128 * RR ^ 3 * As :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  nlinarith

/- English proof (translation)
Take `⟨h1, ⟨c, hc⟩, h3⟩` from `hF`. Conclude with `⟨Formalism.FourierDecayAlt.P.Ux1.ckOn_congr h h1, ⟨c, Formalism.FourierDecayAlt.P.Ux1.cc_congr h hc⟩, fun g hg hne => h3 g hg (by rwa [h g hg])⟩`.
-/
theorem cccoef_congr {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k ρ Wp Wq} {A : ℝ} {mm : ℕ} {ε : ℝ}
    {F F' : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV k ρ, F g = F' g) (hF : JC.CCCoefM Bs A mm ε F) :
    JC.CCCoefM Bs A mm ε F' := by
  obtain ⟨h1, ⟨c, hc⟩, h3⟩ := hF
  exact ⟨Formalism.FourierDecayAlt.P.Ux1.ckOn_congr h h1, ⟨c, Formalism.FourierDecayAlt.P.Ux1.cc_congr h hc⟩,
    fun g hg hne => h3 g hg (by rwa [h g hg])⟩

/- English proof (translation)
Unfold `D.sliceAt`. Rewrite using `[dif_pos hle, dif_pos hle]`. Unfold `U.PhiFun`. Use `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E0) e).integral_comp_comm hint` as an intermediate fact. Conclude with `this.symm ▸ rfl`.
-/
theorem sliceAt_apply {k r : ℕ} {ι : Type} [Fintype ι] {E0 : Type} [NormedAddCommGroup E0] [NormedSpace ℂ E0]
    [CompleteSpace E0] (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → (ι → E0)) (p : C.LPt)
    (hle : D.ptSize p ≤ r) (γ : B.Mat k (r - D.ptSize p)) (e : ι)
    (hint : Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p))) :
    D.sliceAt k r z z' F p γ e = D.sliceAt k r z z' (fun g => F g e) p γ := by
  unfold D.sliceAt
  rw [dif_pos hle, dif_pos hle]
  unfold U.PhiFun
  have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E0) e).integral_comp_comm hint
  exact this.symm ▸ rfl

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P0 T sg w f χ ε h' m i hi hsz hf hfR hχ hε hk2 hh' Kc hKc hK0`. Use `set ph := D.ptSize h' with hph`. Use `set ρ := P0.r - i with hρ`. Establish `e1 : P0.r = ph + (m + 2) + ρ` using `by omega`. Establish `e2 : ph + (m + 2) + ρ = P0.r` using `by omega`.

Establish `hj1 : 1 ≤ ph + (m + 2)` using `by omega`. Establish `hi1 : 1 ≤ i` using `by omega`. Use `set N := w.length with hN`. Use `set z0 := D.castV e1 T.base.z with hz0`. Use `set z0' := D.castV e1 T.base.z' with hz0'`.

Use `set f1 := D.castF e2 f with hf1`. Establish `hLD` using `fun e : Wd.Ix (Fin N) => Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD P0.k (ph + (m + 2)) ρ Wp Wq z0 z0' (by omega) w e hj1`. Use `choose Θ hΘ hΘF using hLD`. Establish `hFrel : ∀ e : Wd.Ix (Fin N), ∀ g ∈ B.GV P0.k (ph + (m + 2) + ρ), U.DjU P0.k (ph + (m + 2)) ρ g ≠ 0 → D.castF e2 (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e) g = B.opApply (Θ e) (fun x => ((χ (Formalism.QuantumDeterminants.Gf P0.k (ph + (m + 2) + ρ) z0 z0' x …`. Introduce `e g hg hD`.

Establish `hFc : B.CkOn ⊤ (B.GV P0.k P0.r) (D.cutF T.base χ f ε)` using `Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hf ε`. Establish `h1 : D.castF e2 (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e) = D.uwG P0.k (ph + (m + 2) + ρ) z0 z0' (D.castF e2 (D.cutF T.base χ f ε)) (ph + (m + 2)) (by omega) w e`. Rewrite using `[Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ (by omega) _ _ w e`. Rewrite using `[h1, hΘF e _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]`.

Use `set σ := D.ptPerm h' with hσ`. Use `set d := D.ptDiag h' with hd_def`. Establish `hd : ∀ q, d q ≠ 0` using `fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h' hh'.1 q q.2`. Use `set dh := (U.hMat σ d).det with hdh_def`. Establish `hdh : dh ≠ 0` using `Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd`.

Use `set wd := (G.wMat (m + 1)).det with hwd_def`. Establish `hwd : wd ≠ 0` using `Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (m + 1)`. Choose the witnesses or unpack the hypotheses as in `⟨r1, hr1, hKr1⟩ : ∃ r1 : ℝ, 0 < r1 ∧ ∀ D ∈ Kc, r1 ≤ ‖D‖ := by`. Break down `Kc.eq_empty_or_nonempty with hE | hne` into its components or cases. Conclude with `⟨1, one_pos, by simp [hE]⟩`.

Take `⟨D0, hD0, hmin⟩` from `hKc.exists_isMinOn hne continuous_norm.continuousOn`. Use `⟨‖D0‖, norm_pos_iff.2 (fun h0 => hK0 (h0 ▸ hD0)), fun D hD => hmin hD⟩` and prove the remaining obligations. Take `⟨r2, hKr2⟩ : ∃ r2 : ℝ, ∀ D ∈ Kc, ‖D‖ ≤ r2` from `hKc.isBounded.exists_norm_le`. Use `set cdw : ℝ := ‖dh * wd‖ with hcdw`. Establish `hcdw0 : 0 < cdw` using `norm_pos_iff.2 (mul_ne_zero hdh hwd)`.

Use `set A1 : ℝ := cdw * r1 / 2 with hA1`. Use `set A2 : ℝ := cdw * max r1 r2 * 2 with hA2`. Establish `hA1p : 0 < A1` using `by positivity`. Establish `hA12 : A1 ≤ A2`. Establish `: r1 ≤ max r1 r2` using `le_max_left _ _`.

Establish `: cdw * r1 ≤ cdw * max r1 r2` using `mul_le_mul_of_nonneg_left this hcdw0.le`. Rewrite using `[hA1, hA2]`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨χD, hχD, hχD1, hχDs⟩` from `bump_annulus hA1p hA12`. Establish `hKj : ∀ D ∈ Kc, A1 < ‖dh * (wd * D)‖ ∧ ‖dh * (wd * D)‖ < A2`.

Introduce `D hD`. Establish `e : ‖dh * (wd * D)‖ = cdw * ‖D‖` using `by rw [← mul_assoc, norm_mul]`. Rewrite using `[e]`. Establish `h1` using `hKr1 D hD`. Establish `h2 : ‖D‖ ≤ max r1 r2` using `(hKr2 D hD).trans (le_max_right _ _)`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[hA1]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hA2]`. Establish `: 0 < max r1 r2` using `lt_of_lt_of_le hr1 (le_max_left _ _)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hA2p : 0 < A2` using `lt_of_lt_of_le hA1p hA12`. Take `⟨δ, hδ, hχε⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Pos.isCutG_scale hχ hε`. Use `set ε'' : ℝ := δ * ε / (2 * A2) ^ 2 with hε''def`. Establish `hε'' : 0 < ε''` using `by positivity`.

Take `⟨C₂, CcG, hUG⟩` from `Formalism.FourierDecayAlt.P.germ_expansion_applies`. Take `⟨CcU, hCU⟩` from `Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis 127 C₂`. Use `set nd : ℕ := 2 * P0.r + P0.k + 1 with hnd`. Use `set X : ℕ := N * nd ^ 2 + nd ^ 3 with hX`. Use `set o : ℕ := N * (ph + (m + 2)) with ho`.

Use `set κ : ℕ := N * (ph + (m + 2)) + N * (ph + (m + 2)) ^ 2 with hκ`. Use `set mmB : ℕ := P5.mmUser P0 N + (5 + (2 * (P0.r - i) + P0.k + 1) * N) with hmmB`. Use `set As : ℕ := (11 * X + 5) + o + (κ + (ph + (m + 1 + 1)) * o) + mmB + (2 * (ph + (m + 1 + 1) + ρ) + P0.k + 1) ^ 3 + (C₂ * (ph + (m + 1 + 1) + ρ + 1) ^ 2 + 1) with hAs`. Set `UD : U.UData P0.k ph (m + 1 + 1) ρ Wp Wq (Wd.Ix (Fin N))` to `⟨σ, d, z0, z0', Θ, χD, fun x => χ (ε⁻¹ * x), δ * ε, ε'', o, κ, 0, mmB, As⟩`. Establish `hOk : UD.Ok C₂`.

Use `⟨hd, by omega, Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem, Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem, fun e => hΘ e, hχD, hχε, hε'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `h2` using `hχDs x hx`. Establish `h3 : ‖x‖ ^ 2 ≤ (2 * A2) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) h2 2`. Combine the equalities or inequalities in the displayed calculation.

Establish `: (2 * A2) ^ 2 ≠ 0` using `by positivity`. Rewrite using `[hε''def, div_mul_cancel₀ _ this]`. Use `show o ≤ As`. Use linear arithmetic over natural numbers and integers. Use `show κ + (ph + (m + 1 + 1)) * o ≤ As`.

Use linear arithmetic over natural numbers and integers. Use `show ((0 : ℝ)) ≤ (As : ℝ)`. Check the signs of the components of the expression. Use `show mmB ≤ As`. Use linear arithmetic over natural numbers and integers.

Use `show (2 * (ph + (m + 1 + 1) + ρ) + P0.k + 1) ^ 3 ≤ As`. Use linear arithmetic over natural numbers and integers. Use `show C₂ * (ph + (m + 1 + 1) + ρ + 1) ^ 2 + 1 ≤ As`. Use linear arithmetic over natural numbers and integers. Use `set RR : ℝ := ((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1 with hRR`.

Establish `hRR1 : 1 ≤ RR` using `by rw [hRR]; have : (0 : ℝ) ≤ ((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _; linarith`. Use `set R4 : ℝ := RR ^ 4 * (As : ℝ) with hR4`. Establish `hR40 : 0 ≤ R4` using `by positivity`. Use `set A₀ : ℝ := (|CcG| + |CcU|) * R4 with hA₀def`. Establish `hA₀G : CcG * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) ≤ A₀`.

Establish `e : CcG * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) = CcG * R4` using `by show _ = CcG * (RR ^ 4 * (As : ℝ)); rw [hRR]; ring`. Rewrite using `[e, hA₀def]`. Combine the equalities or inequalities in the displayed calculation. Establish `hA₀U : CcU * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) ≤ A₀`. Establish `e : CcU * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) = CcU * R4` using `by show _ = CcU * (RR ^ 4 * (As : ℝ)); rw [hRR]; ring`.

Rewrite using `[e, hA₀def]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨Rf, hRf⟩` from `hfR`. Establish `hf1s : B.CkOn ⊤ (B.GV P0.k (ph + (m + 1 + 1) + ρ)) f1` using `Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hf`. Establish `hf1c : ∀ (A : ℝ) (mm : ℕ), B.InCC A mm f1`.

Introduce `A mm`. Use `Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hf1s (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P0.k _ Rf) (fun g hg hgC => ?_) A mm` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hgC` to reduce the goal to its premises. Establish `h1` using `hRf _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hg) hne`.

Rewrite `h1` using `[Formalism.FourierDecayAlt.P.PBE.gN_castM]`. Then use the resulting hypothesis. Take `⟨c, hc⟩` from `hf1c A₀ (3 * UD.As)`. Take `⟨V, indexVFirst, indexVSecond, hVc, ⟨MM⟩⟩` from `Formalism.FourierDecayAlt.P.compactly_supported_banach_model P0.k ρ (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) (UD.a C₂ A₀) UD.mmB UD.S`. Use `letI := indexVFirst`. Use `letI := indexVSecond`.

Use `haveI := hVc`. Take `⟨-, hKg⟩` from `hUG P0.k ph m ρ Wp Wq (Wd.Ix (Fin N)) UD hOk A₀ hA₀G`. Take `⟨Cst, hCst⟩` from `hKg Kc hKc hK0`. Take `⟨Φ, hΦev, hΦg⟩` from `hCst f1 c hc V MM`. Take `⟨ha1, -, -, Cd, hCd⟩` from `hCU P0.k ph (m + 1 + 1) ρ Wp Wq (Wd.Ix (Fin N)) UD hOk A₀ hA₀U`.

Take `⟨Φ', hΦ'ev, hΦ'reg⟩` from `hCd f1 c hc V MM`. Establish `hΦΦ' : ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 → Φ Z = Φ' Z`. Introduce `Z hZ`. Establish `h0 : ∀ γ ∈ B.GV P0.k ρ, (fun _ : B.Mat P0.k ρ => (0 : Wd.Ix (Fin N) → (Wq →L[ℂ] Wp))) γ = MM.ev (Φ Z - Φ' Z) γ`. Introduce `γ hγ`.

Rewrite using `[map_sub, Pi.sub_apply, hΦev Z hZ γ hγ, hΦ'ev Z hZ γ hγ, sub_self]`. Establish `hcc` using `Formalism.FourierDecayAlt.P.Ux1.cc_congr h0 (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (A := UD.a C₂ A₀) (m := UD.mmB))`. Use `MM.least _ 0 hcc` as an intermediate fact. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 this)`. Establish `hAs1 : (1 : ℝ) ≤ (As : ℝ)`.

Establish `: 1 ≤ As` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `ha128 : 128 * RR ^ 3 * (As : ℝ) ≤ UD.a C₂ A₀`. Establish `h` using `ha1`. Rewrite using `[hRR]`.

Evaluate the numerical expressions using `at h ⊢`. Conclude with `h`. Establish `hRm : (m : ℝ) + 3 ≤ RR`. Rewrite using `[hRR]`. Use `push_cast`.

Establish `: (0 : ℝ) ≤ (ph : ℝ)` using `Nat.cast_nonneg _`. Establish `: (0 : ℝ) ≤ (ρ : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hma : ((m : ℝ) + 1) * ((m : ℝ) + 4) < UD.a C₂ A₀` using `arith_ma _ _ _ _ (Nat.cast_nonneg m) hRm hAs1 ha128`. Establish `hRr : RR = (P0.r : ℝ) + 1` using `by rw [hRR, e2]`.

Establish `hAa : P5.Auser P0 N + 1 ≤ UD.a C₂ A₀`. Establish `hX1 : ((11 * X + 5 : ℕ) : ℝ) ≤ (As : ℝ)`. Establish `: 11 * X + 5 ≤ As` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hXr : ((N : ℝ) * (P5.nV P0 : ℝ) ^ 2 + (P5.nV P0 : ℝ) ^ 3) = (X : ℝ)`.

Rewrite using `[hX, hnd]`. Simplify using `[P5.nV]`. Unfold `P5.Auser`. Rewrite using `[hXr, ← hRr]`. Establish `hX0 : (0 : ℝ) ≤ X` using `Nat.cast_nonneg _`.

Move the coercions through the operations in `at hX1`. Establish `hR3 : 1 ≤ RR ^ 3` using `one_le_pow₀ hRR1`. Use the polynomial consequences of the given equalities and inequalities. Establish `hdetc : IsOpen {Z : G.Mat (m + 1 + 1) | G.detM Z ≠ 0}`. Use `isOpen_ne_fun ?_ continuous_const` and prove the remaining obligations.

Unfold `G.detM`. Conclude with `Continuous.matrix_det (continuous_id (X := Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ))`. Establish `hdec : ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 → ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ (Cd * c) * (1 + ‖Z‖) ^ (-UD.a C₂ A₀)`. Introduce `Z hZ`. Establish `hev : Φ =ᶠ[nhds Z] Φ'` using `by filter_upwards [hdetc.mem_nhds hZ] with Z' hZ' using hΦΦ' Z' hZ'`.

Use `⟨(hΦ'reg Z hZ).1.continuousAt.congr hev.symm, ?_⟩` and prove the remaining obligations. Establish `h` using `(hΦ'reg Z hZ).2 0 (Nat.zero_le _)`. Rewrite `h` using `[norm_iteratedFDeriv_zero]`. Rewrite using `[hΦΦ' Z hZ]`. Conclude with `h`.

Establish `hLex : ∀ γ ∈ B.GV P0.k ρ, ∃ L : V →L[ℂ] (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)), ∀ v, L v = MM.ev v γ`. Introduce `γ hγ`. Establish `hgN : 0 < B.gN γ ^ UD.a C₂ A₀` using `Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.Ux1.gN_pos hγ) _`. Set `L₀ : V →ₗ[ℂ] (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp))` to `(LinearMap.proj (R := ℂ) (φ := fun _ : B.Mat P0.k ρ => Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) γ) ∘ₗ MM.ev`. Establish `hbd : ∀ v, ‖L₀ v‖ ≤ (B.gN γ ^ UD.a C₂ A₀)⁻¹ * ‖v‖`.

Introduce `v`. Establish `h1` using `(MM.mem v).2 [] [] (by simp) (by simp) (by simp) γ hγ`. Rewrite using `[inv_mul_eq_div, le_div_iff₀' hgN]`. Conclude with `h1`. Conclude with `⟨L₀.mkContinuous _ hbd, fun v => rfl⟩`.

Use `set Fι : B.Mat P0.k P0.r → (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) := fun g e => D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e g with hFι`. Establish `hO : IsOpen {x : B.Mat P0.k (ph + (m + 1 + 1) + ρ) | A1 < ‖U.DjU P0.k (ph + (m + 1 + 1)) ρ x‖ ∧ ‖U.DjU P0.k (ph + (m + 1 + 1)) ρ x‖ < A2}`. Establish `hc` using `(Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU P0.k (ph + (m + 1 + 1)) ρ).norm`. Conclude with `(isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)`. Establish `hread : ∀ γ ∈ B.GV P0.k ρ, ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 → G.detM Z ∈ (fun D => wd * D) '' Kc → MM.ev (Φ Z) γ = U.PhiFun P0.k ρ σ d (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e1.symm Fι) Z γ`.

Introduce `γ hγ Z hZ hZK`. Take `⟨D0, hD0, hZD⟩` from `hZK`. Rewrite using `[hΦev Z hZ γ hγ]`. Unfold `U.UData.Phi U.PhiFun`. Use `integral_congr_ae (Eventually.of_forall fun ξ => ?_)` and prove the remaining obligations.

Simplify using `only`. Use `congr 1`. Use function extensionality and compare the values at `e`. Establish `hg` using `Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ Z hZ hγ`. Establish `hDj : U.DjU P0.k (ph + (m + 1 + 1)) ρ (U.gaXi P0.k ρ σ d ξ Z γ) = dh * (wd * D0)`.

Rewrite using `[Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, ← hZD]`. Establish `hb` using `hKj D0 hD0`. Rewrite `hb` using `[← hDj]`. Establish `hDj0 : U.DjU P0.k (ph + (m + 1 + 1)) ρ (U.gaXi P0.k ρ σ d ξ Z γ) ≠ 0`. Introduce `h0`.

Rewrite `hb` using `[h0, norm_zero]`. Combine the linear relations using `[hb.1]`. Establish `hF` using `hFrel e _ hg hDj0`. Simplify using `only [U.UData.F1]`. Use `(Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open (Θ e) hO (fun x hx => ?_) _ hb).trans hF.symm` and prove the remaining obligations.

Use `show (χD (U.DjU P0.k (ph + (m + 1 + 1)) ρ x) * ((χ (ε⁻¹ * Formalism.QuantumDeterminants.Gf P0.k (ph + (m + 1 + 1) + ρ) z0 z0' x) : ℝ) : ℂ)) • f1 x = _`. Rewrite using `[hχD1 _ hx.1.le hx.2.le, one_mul, div_eq_inv_mul]`. Establish `hev_slv : ∀ q, okG m Kc q → ∀ γ ∈ B.GV P0.k ρ, ∀ e, MM.ev (yG U.betaU m Φ q) γ e = KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q) (by rw [ptSize_ptG, hsz]) e γ`. Introduce `q hq γ hγ e`. Take `⟨L, hL⟩` from `hLex γ hγ`.

Establish `hloc : D.IsLocPt (ptG h' m q) i` using `hsz ▸ isLocPt_ptG hh' hK0 hq`. Establish `hle : D.ptSize (ptG h' m q) ≤ P0.r` using `by rw [ptSize_ptG]; omega`. Establish `hγ' : D.castM (by rw [ptSize_ptG]; omega : ρ = P0.r - D.ptSize (ptG h' m q)) γ ∈ B.GV P0.k (P0.r - D.ptSize (ptG h' m q))` using `Formalism.FourierDecayAlt.P.PBE.castM_GV _ hγ`. Establish `hint : Integrable (fun ξ : U.Xi P0.k (D.ptSize (ptG h' m q)) 0 (P0.r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) => U.psiStar P0.k (P0.r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.castV (by rw [ptSize_ptG]; omega) T.base.z) (D.castV (by rw [ptSize_ptG]; omega) T.bas …`. Use `integrable_pi_iff.2 fun e' => ?_` and prove the remaining obligations.

Conclude with `hSI Wp Wq P0 T w f χ ε i hi hi1 hk2 hf ⟨Rf, hRf⟩ hχ hε _ hloc e' _ hγ'`. Establish `hY` using `hYG P0.k P0.r (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) T.base.z T.base.z' Fι h' m ρ e1 V Φ L γ Kc (Cd * c) (UD.a C₂ A₀) hh' hK0 hma hdec (fun Z hZ hZK => by rw [hL]; exact hread γ hγ Z hZ hZK) q hq hint`. Rewrite using `[← hL, hY, sliceAt_apply _ _ _ _ hle _ e hint]`. Both sides reduce to the same expression. Establish `hz1 : U.lowV P0.k (ph + (m + 1 + 1)) ρ z0 = (T.bs i).z`.

Establish `hzl : T.base.z = D.castV (by omega) (Formalism.QuantumDeterminants.liftVec P0.k i (P0.r - i) (T.bs i).z)` using `(T.z_lev i hi).symm`. Rewrite using `[hz0, hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec (by omega) _ _`. Establish `hz1' : U.lowV P0.k (ph + (m + 1 + 1)) ρ z0' = (T.bs i).z'`. Establish `hzl : T.base.z' = D.castV (by omega) (Formalism.QuantumDeterminants.liftVec P0.k i (P0.r - i) (T.bs i).z')` using `(T.z'_lev i hi).symm`.

Rewrite using `[hz0', hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec (by omega) _ _`. Establish `hSg : ∀ γ ∈ UD.S, ε'' ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - i) (T.bs i).z (T.bs i).z' γ`. Introduce `γ hγ`. Establish `h` using `hγ`.

Simplify using `only [U.UData.S, Set.mem_ofPred_eq] at h`. Rewrite using `[← hz1, ← hz1']`. Conclude with `h`. Take `⟨Bf, Cp, hCp0, hBf, hBfx⟩` from `hFM Wp Wq P0 T sg ⟨i, by omega⟩ w (UD.a C₂ A₀) UD.mmB ε'' UD.S hε'' hAa (by show P5.mmUser P0 N ≤ mmB; omega) (by show 5 + (2 * (P0.r - i) + P0.k + 1) * N ≤ mmB; omega) hSg V MM`. Establish `hcls : ∀ (v : V) (e : Wd.Ix (Fin N)), JC.CCCoefM (T.bs i) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (fun γ => MM.ev v γ e)`.

Introduce `v e`. Establish `h1 : B.CCle (UD.a C₂ A₀) UD.mmB (fun γ => MM.ev v γ e) ‖v‖` using `ccle_comp (MM.mem v) e`. Establish `h2 : B.CCle (P5.Auser P0 N + 1) UD.mmB (fun γ => MM.ev v γ e) ‖v‖` using `Formalism.FourierDecayAlt.P.compactly_supported_monotone P0.k ρ _ (UD.a C₂ A₀) _ ‖v‖ UD.mmB _ hAa h1`. Establish `h3 : B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (fun γ => MM.ev v γ e) ‖v‖` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by show P5.mmUser P0 N ≤ mmB; omega) h2`. Use `⟨h3.1, ⟨_, h3⟩, fun γ hγ hne => ?_⟩` and prove the remaining obligations.

Establish `hS : γ ∈ UD.S`. Assume the negation of the conclusion as `hn`. Apply `hne` to reduce the goal to its premises. Use `show MM.ev v γ e = 0`. Rewrite using `[MM.off v γ hγ hn]`.

Both sides reduce to the same expression. Conclude with `hSg γ hS`. Establish `hform : ∀ q1 q2, okG m Kc q1 → okG m Kc q2 → D.formLev T sg ⟨i, by omega⟩ w (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q1) (by rw [ptSize_ptG, hsz])) (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q2) (by rw [ptSize_ptG, hsz])) = Bf (yG U.betaU m Φ q1) (yG U.betaU m Φ q2)`. Introduce `q1 q2 hq1 hq2`. Use `(hBfx _ _ _ _ ε'' hε'' (fun e => ?_) (fun e => ?_) (fun e γ hγ => hev_slv q1 hq1 γ hγ e) (fun e γ hγ => hev_slv q2 hq2 γ hγ e)).symm` and prove the remaining obligations.

Conclude with `cccoef_congr (fun γ hγ => hev_slv q1 hq1 γ hγ e) (hcls _ e)`. Conclude with `cccoef_congr (fun γ hγ => hev_slv q2 hq2 γ hγ e) (hcls _ e)`. Conclude with `⟨V, indexVFirst, indexVSecond, hVc, Bf, Φ, Cp, Cst * c, hCp0, hBf, hform, fun t D ht hD => hΦg t D ht hD⟩`.
-/
theorem germPlace_of (hSI : SliceIntCut) (hYG : YGSlice) (hFM : FormModel) : GermPlace := by
  intro Wp Wq _ _ _ _ _ _ P0 T sg w f χ ε h' m i hi hsz hf hfR hχ hε hk2 hh' Kc hKc hK0
  classical

  set ph := D.ptSize h' with hph
  set ρ := P0.r - i with hρ
  have e1 : P0.r = ph + (m + 2) + ρ := by omega
  have e2 : ph + (m + 2) + ρ = P0.r := by omega
  have hj1 : 1 ≤ ph + (m + 2) := by omega
  have hi1 : 1 ≤ i := by omega
  set N := w.length with hN
  set z0 := D.castV e1 T.base.z with hz0
  set z0' := D.castV e1 T.base.z' with hz0'
  set f1 := D.castF e2 f with hf1

  have hLD := fun e : Wd.Ix (Fin N) =>
    Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD P0.k (ph + (m + 2)) ρ Wp Wq z0 z0' (by omega) w e hj1
  choose Θ hΘ hΘF using hLD
  have hFrel : ∀ e : Wd.Ix (Fin N), ∀ g ∈ B.GV P0.k (ph + (m + 2) + ρ), U.DjU P0.k (ph + (m + 2)) ρ g ≠ 0 →
      D.castF e2 (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e) g =
        B.opApply (Θ e) (fun x => ((χ (Formalism.QuantumDeterminants.Gf P0.k (ph + (m + 2) + ρ) z0 z0' x / ε) : ℝ) : ℂ) • f1 x) g := by
    intro e g hg hD
    have hFc : B.CkOn ⊤ (B.GV P0.k P0.r) (D.cutF T.base χ f ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hf ε
    have h1 : D.castF e2 (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e) =
        D.uwG P0.k (ph + (m + 2) + ρ) z0 z0' (D.castF e2 (D.cutF T.base χ f ε)) (ph + (m + 2)) (by omega) w e := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ (by omega) _ _ w e
    rw [h1, hΘF e _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]

  set σ := D.ptPerm h' with hσ
  set d := D.ptDiag h' with hd_def
  have hd : ∀ q, d q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h' hh'.1 q q.2
  set dh := (U.hMat σ d).det with hdh_def
  have hdh : dh ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd
  set wd := (G.wMat (m + 1)).det with hwd_def
  have hwd : wd ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (m + 1)

  obtain ⟨r1, hr1, hKr1⟩ : ∃ r1 : ℝ, 0 < r1 ∧ ∀ D ∈ Kc, r1 ≤ ‖D‖ := by
    rcases Kc.eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, by simp [hE]⟩
    · obtain ⟨D0, hD0, hmin⟩ := hKc.exists_isMinOn hne continuous_norm.continuousOn
      refine ⟨‖D0‖, norm_pos_iff.2 (fun h0 => hK0 (h0 ▸ hD0)), fun D hD => hmin hD⟩
  obtain ⟨r2, hKr2⟩ : ∃ r2 : ℝ, ∀ D ∈ Kc, ‖D‖ ≤ r2 := hKc.isBounded.exists_norm_le
  set cdw : ℝ := ‖dh * wd‖ with hcdw
  have hcdw0 : 0 < cdw := norm_pos_iff.2 (mul_ne_zero hdh hwd)
  set A1 : ℝ := cdw * r1 / 2 with hA1
  set A2 : ℝ := cdw * max r1 r2 * 2 with hA2
  have hA1p : 0 < A1 := by positivity
  have hA12 : A1 ≤ A2 := by
    have : r1 ≤ max r1 r2 := le_max_left _ _
    have : cdw * r1 ≤ cdw * max r1 r2 := mul_le_mul_of_nonneg_left this hcdw0.le
    rw [hA1, hA2]; nlinarith
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := bump_annulus hA1p hA12
  have hKj : ∀ D ∈ Kc, A1 < ‖dh * (wd * D)‖ ∧ ‖dh * (wd * D)‖ < A2 := by
    intro D hD
    have e : ‖dh * (wd * D)‖ = cdw * ‖D‖ := by rw [← mul_assoc, norm_mul]
    rw [e]
    have h1 := hKr1 D hD
    have h2 : ‖D‖ ≤ max r1 r2 := (hKr2 D hD).trans (le_max_right _ _)
    constructor
    · rw [hA1]; nlinarith
    · rw [hA2]
      have : 0 < max r1 r2 := lt_of_lt_of_le hr1 (le_max_left _ _)
      nlinarith
  have hA2p : 0 < A2 := lt_of_lt_of_le hA1p hA12
  obtain ⟨δ, hδ, hχε⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.isCutG_scale hχ hε
  set ε'' : ℝ := δ * ε / (2 * A2) ^ 2 with hε''def
  have hε'' : 0 < ε'' := by positivity

  obtain ⟨C₂, CcG, hUG⟩ := Formalism.FourierDecayAlt.P.germ_expansion_applies
  obtain ⟨CcU, hCU⟩ := Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis 127 C₂
  set nd : ℕ := 2 * P0.r + P0.k + 1 with hnd
  set X : ℕ := N * nd ^ 2 + nd ^ 3 with hX
  set o : ℕ := N * (ph + (m + 2)) with ho
  set κ : ℕ := N * (ph + (m + 2)) + N * (ph + (m + 2)) ^ 2 with hκ
  set mmB : ℕ := P5.mmUser P0 N + (5 + (2 * (P0.r - i) + P0.k + 1) * N) with hmmB
  set As : ℕ := (11 * X + 5) + o + (κ + (ph + (m + 1 + 1)) * o) + mmB +
    (2 * (ph + (m + 1 + 1) + ρ) + P0.k + 1) ^ 3 + (C₂ * (ph + (m + 1 + 1) + ρ + 1) ^ 2 + 1) with hAs
  let UD : U.UData P0.k ph (m + 1 + 1) ρ Wp Wq (Wd.Ix (Fin N)) :=
    ⟨σ, d, z0, z0', Θ, χD, fun x => χ (ε⁻¹ * x), δ * ε, ε'', o, κ, 0, mmB, As⟩
  have hOk : UD.Ok C₂ := by
    refine ⟨hd, by omega, Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem,
      Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem, fun e => hΘ e, hχD, hχε, hε'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have h2 := hχDs x hx
      have h3 : ‖x‖ ^ 2 ≤ (2 * A2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc ε'' * ‖x‖ ^ 2 ≤ ε'' * (2 * A2) ^ 2 := mul_le_mul_of_nonneg_left h3 hε''.le
        _ = δ * ε := by
          have : (2 * A2) ^ 2 ≠ 0 := by positivity
          rw [hε''def, div_mul_cancel₀ _ this]
    · show o ≤ As; omega
    · show κ + (ph + (m + 1 + 1)) * o ≤ As; omega
    · show ((0 : ℝ)) ≤ (As : ℝ); positivity
    · show mmB ≤ As; omega
    · show (2 * (ph + (m + 1 + 1) + ρ) + P0.k + 1) ^ 3 ≤ As; omega
    · show C₂ * (ph + (m + 1 + 1) + ρ + 1) ^ 2 + 1 ≤ As; omega

  set RR : ℝ := ((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1 with hRR
  have hRR1 : 1 ≤ RR := by rw [hRR]; have : (0 : ℝ) ≤ ((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  set R4 : ℝ := RR ^ 4 * (As : ℝ) with hR4
  have hR40 : 0 ≤ R4 := by positivity
  set A₀ : ℝ := (|CcG| + |CcU|) * R4 with hA₀def
  have hA₀G : CcG * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) ≤ A₀ := by
    have e : CcG * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) = CcG * R4 := by
      show _ = CcG * (RR ^ 4 * (As : ℝ)); rw [hRR]; ring
    rw [e, hA₀def]
    calc CcG * R4 ≤ |CcG| * R4 := mul_le_mul_of_nonneg_right (le_abs_self _) hR40
      _ ≤ (|CcG| + |CcU|) * R4 := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg CcU]) hR40
  have hA₀U : CcU * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) ≤ A₀ := by
    have e : CcU * (((ph + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (UD.As : ℝ) = CcU * R4 := by
      show _ = CcU * (RR ^ 4 * (As : ℝ)); rw [hRR]; ring
    rw [e, hA₀def]
    calc CcU * R4 ≤ |CcU| * R4 := mul_le_mul_of_nonneg_right (le_abs_self _) hR40
      _ ≤ (|CcG| + |CcU|) * R4 := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg CcG]) hR40
  obtain ⟨Rf, hRf⟩ := hfR
  have hf1s : B.CkOn ⊤ (B.GV P0.k (ph + (m + 1 + 1) + ρ)) f1 := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hf
  have hf1c : ∀ (A : ℝ) (mm : ℕ), B.InCC A mm f1 := by
    intro A mm
    refine Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hf1s (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P0.k _ Rf) (fun g hg hgC => ?_) A mm
    by_contra hne
    apply hgC
    have h1 := hRf _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hg) hne
    rwa [Formalism.FourierDecayAlt.P.PBE.gN_castM] at h1
  obtain ⟨c, hc⟩ := hf1c A₀ (3 * UD.As)

  obtain ⟨V, indexVFirst, indexVSecond, hVc, ⟨MM⟩⟩ :=
    Formalism.FourierDecayAlt.P.compactly_supported_banach_model P0.k ρ (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) (UD.a C₂ A₀) UD.mmB UD.S
  letI := indexVFirst; letI := indexVSecond; haveI := hVc
  obtain ⟨-, hKg⟩ := hUG P0.k ph m ρ Wp Wq (Wd.Ix (Fin N)) UD hOk A₀ hA₀G
  obtain ⟨Cst, hCst⟩ := hKg Kc hKc hK0
  obtain ⟨Φ, hΦev, hΦg⟩ := hCst f1 c hc V MM
  obtain ⟨ha1, -, -, Cd, hCd⟩ := hCU P0.k ph (m + 1 + 1) ρ Wp Wq (Wd.Ix (Fin N)) UD hOk A₀ hA₀U
  obtain ⟨Φ', hΦ'ev, hΦ'reg⟩ := hCd f1 c hc V MM
  have hΦΦ' : ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 → Φ Z = Φ' Z := by
    intro Z hZ
    have h0 : ∀ γ ∈ B.GV P0.k ρ, (fun _ : B.Mat P0.k ρ => (0 : Wd.Ix (Fin N) → (Wq →L[ℂ] Wp))) γ =
        MM.ev (Φ Z - Φ' Z) γ := by
      intro γ hγ
      rw [map_sub, Pi.sub_apply, hΦev Z hZ γ hγ, hΦ'ev Z hZ γ hγ, sub_self]
    have hcc := Formalism.FourierDecayAlt.P.Ux1.cc_congr h0 (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (A := UD.a C₂ A₀) (m := UD.mmB))
    have := MM.least _ 0 hcc
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

  have hAs1 : (1 : ℝ) ≤ (As : ℝ) := by
    have : 1 ≤ As := by omega
    exact_mod_cast this
  have ha128 : 128 * RR ^ 3 * (As : ℝ) ≤ UD.a C₂ A₀ := by
    have h := ha1
    rw [hRR]; norm_num at h ⊢; exact h
  have hRm : (m : ℝ) + 3 ≤ RR := by
    rw [hRR]; push_cast
    have : (0 : ℝ) ≤ (ph : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (ρ : ℝ) := Nat.cast_nonneg _
    linarith
  have hma : ((m : ℝ) + 1) * ((m : ℝ) + 4) < UD.a C₂ A₀ := arith_ma _ _ _ _ (Nat.cast_nonneg m) hRm hAs1 ha128
  have hRr : RR = (P0.r : ℝ) + 1 := by rw [hRR, e2]
  have hAa : P5.Auser P0 N + 1 ≤ UD.a C₂ A₀ := by
    have hX1 : ((11 * X + 5 : ℕ) : ℝ) ≤ (As : ℝ) := by
      have : 11 * X + 5 ≤ As := by omega
      exact_mod_cast this
    have hXr : ((N : ℝ) * (P5.nV P0 : ℝ) ^ 2 + (P5.nV P0 : ℝ) ^ 3) = (X : ℝ) := by
      rw [hX, hnd]; simp [P5.nV]
    unfold P5.Auser
    rw [hXr, ← hRr]
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
    push_cast at hX1
    have hR3 : 1 ≤ RR ^ 3 := one_le_pow₀ hRR1
    nlinarith
  have hdetc : IsOpen {Z : G.Mat (m + 1 + 1) | G.detM Z ≠ 0} := by
    refine isOpen_ne_fun ?_ continuous_const
    unfold G.detM
    exact Continuous.matrix_det (continuous_id (X := Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ))
  have hdec : ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 → ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ (Cd * c) * (1 + ‖Z‖) ^ (-UD.a C₂ A₀) := by
    intro Z hZ
    have hev : Φ =ᶠ[nhds Z] Φ' := by
      filter_upwards [hdetc.mem_nhds hZ] with Z' hZ' using hΦΦ' Z' hZ'
    refine ⟨(hΦ'reg Z hZ).1.continuousAt.congr hev.symm, ?_⟩
    have h := (hΦ'reg Z hZ).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    rw [hΦΦ' Z hZ]
    exact h

  have hLex : ∀ γ ∈ B.GV P0.k ρ, ∃ L : V →L[ℂ] (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)), ∀ v, L v = MM.ev v γ := by
    intro γ hγ
    have hgN : 0 < B.gN γ ^ UD.a C₂ A₀ := Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.Ux1.gN_pos hγ) _
    let L₀ : V →ₗ[ℂ] (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : B.Mat P0.k ρ => Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) γ) ∘ₗ MM.ev
    have hbd : ∀ v, ‖L₀ v‖ ≤ (B.gN γ ^ UD.a C₂ A₀)⁻¹ * ‖v‖ := by
      intro v
      have h1 := (MM.mem v).2 [] [] (by simp) (by simp) (by simp) γ hγ
      rw [inv_mul_eq_div, le_div_iff₀' hgN]
      exact h1
    exact ⟨L₀.mkContinuous _ hbd, fun v => rfl⟩

  set Fι : B.Mat P0.k P0.r → (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) :=
    fun g e => D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e g with hFι
  have hO : IsOpen {x : B.Mat P0.k (ph + (m + 1 + 1) + ρ) |
      A1 < ‖U.DjU P0.k (ph + (m + 1 + 1)) ρ x‖ ∧ ‖U.DjU P0.k (ph + (m + 1 + 1)) ρ x‖ < A2} := by
    have hc := (Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU P0.k (ph + (m + 1 + 1)) ρ).norm
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hread : ∀ γ ∈ B.GV P0.k ρ, ∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 →
      G.detM Z ∈ (fun D => wd * D) '' Kc →
      MM.ev (Φ Z) γ = U.PhiFun P0.k ρ σ d (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e1.symm Fι) Z γ := by
    intro γ hγ Z hZ hZK
    obtain ⟨D0, hD0, hZD⟩ := hZK
    rw [hΦev Z hZ γ hγ]
    unfold U.UData.Phi U.PhiFun
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    congr 1
    funext e
    have hg := Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ Z hZ hγ
    have hDj : U.DjU P0.k (ph + (m + 1 + 1)) ρ (U.gaXi P0.k ρ σ d ξ Z γ) = dh * (wd * D0) := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, ← hZD]
    have hb := hKj D0 hD0
    rw [← hDj] at hb
    have hDj0 : U.DjU P0.k (ph + (m + 1 + 1)) ρ (U.gaXi P0.k ρ σ d ξ Z γ) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hb; linarith [hb.1]
    have hF := hFrel e _ hg hDj0
    simp only [U.UData.F1]
    refine (Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open (Θ e) hO (fun x hx => ?_) _ hb).trans hF.symm
    show (χD (U.DjU P0.k (ph + (m + 1 + 1)) ρ x) *
      ((χ (ε⁻¹ * Formalism.QuantumDeterminants.Gf P0.k (ph + (m + 1 + 1) + ρ) z0 z0' x) : ℝ) : ℂ)) • f1 x = _
    rw [hχD1 _ hx.1.le hx.2.le, one_mul, div_eq_inv_mul]

  have hev_slv : ∀ q, okG m Kc q → ∀ γ ∈ B.GV P0.k ρ, ∀ e,
      MM.ev (yG U.betaU m Φ q) γ e =
        KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q) (by rw [ptSize_ptG, hsz]) e γ := by
    intro q hq γ hγ e
    obtain ⟨L, hL⟩ := hLex γ hγ
    have hloc : D.IsLocPt (ptG h' m q) i := hsz ▸ isLocPt_ptG hh' hK0 hq
    have hle : D.ptSize (ptG h' m q) ≤ P0.r := by rw [ptSize_ptG]; omega
    have hγ' : D.castM (by rw [ptSize_ptG]; omega : ρ = P0.r - D.ptSize (ptG h' m q)) γ ∈
        B.GV P0.k (P0.r - D.ptSize (ptG h' m q)) := Formalism.FourierDecayAlt.P.PBE.castM_GV _ hγ
    have hint : Integrable (fun ξ : U.Xi P0.k (D.ptSize (ptG h' m q)) 0 (P0.r - D.ptSize (ptG h' m q))
          (D.ptPerm (ptG h' m q)) =>
        U.psiStar P0.k (P0.r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q))
          (D.castV (by rw [ptSize_ptG]; omega) T.base.z) (D.castV (by rw [ptSize_ptG]; omega) T.base.z') ξ •
          D.castF (by rw [ptSize_ptG]; omega) Fι
            (U.gaXi P0.k (P0.r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.ptDiag (ptG h' m q)) ξ
              (fun a => a.elim0) (D.castM (by rw [ptSize_ptG]; omega) γ)))
        (U.muXi P0.k (D.ptSize (ptG h' m q)) 0 (P0.r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q))) := by
      refine integrable_pi_iff.2 fun e' => ?_
      exact hSI Wp Wq P0 T w f χ ε i hi hi1 hk2 hf ⟨Rf, hRf⟩ hχ hε _ hloc e' _ hγ'
    have hY := hYG P0.k P0.r (Wd.Ix (Fin N) → (Wq →L[ℂ] Wp)) T.base.z T.base.z' Fι h' m ρ e1 V Φ L γ Kc
      (Cd * c) (UD.a C₂ A₀) hh' hK0 hma hdec
      (fun Z hZ hZK => by rw [hL]; exact hread γ hγ Z hZ hZK) q hq hint
    rw [← hL, hY, sliceAt_apply _ _ _ _ hle _ e hint]
    rfl

  have hz1 : U.lowV P0.k (ph + (m + 1 + 1)) ρ z0 = (T.bs i).z := by
    have hzl : T.base.z = D.castV (by omega) (Formalism.QuantumDeterminants.liftVec P0.k i (P0.r - i) (T.bs i).z) := (T.z_lev i hi).symm
    rw [hz0, hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec (by omega) _ _
  have hz1' : U.lowV P0.k (ph + (m + 1 + 1)) ρ z0' = (T.bs i).z' := by
    have hzl : T.base.z' = D.castV (by omega) (Formalism.QuantumDeterminants.liftVec P0.k i (P0.r - i) (T.bs i).z') := (T.z'_lev i hi).symm
    rw [hz0', hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec (by omega) _ _
  have hSg : ∀ γ ∈ UD.S, ε'' ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - i) (T.bs i).z (T.bs i).z' γ := by
    intro γ hγ
    have h := hγ
    simp only [U.UData.S, Set.mem_ofPred_eq] at h
    rw [← hz1, ← hz1']
    exact h
  obtain ⟨Bf, Cp, hCp0, hBf, hBfx⟩ := hFM Wp Wq P0 T sg ⟨i, by omega⟩ w (UD.a C₂ A₀) UD.mmB ε'' UD.S hε''
    hAa (by show P5.mmUser P0 N ≤ mmB; omega) (by show 5 + (2 * (P0.r - i) + P0.k + 1) * N ≤ mmB; omega) hSg V MM
  have hcls : ∀ (v : V) (e : Wd.Ix (Fin N)),
      JC.CCCoefM (T.bs i) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (fun γ => MM.ev v γ e) := by
    intro v e
    have h1 : B.CCle (UD.a C₂ A₀) UD.mmB (fun γ => MM.ev v γ e) ‖v‖ := ccle_comp (MM.mem v) e
    have h2 : B.CCle (P5.Auser P0 N + 1) UD.mmB (fun γ => MM.ev v γ e) ‖v‖ :=
      Formalism.FourierDecayAlt.P.compactly_supported_monotone P0.k ρ _ (UD.a C₂ A₀) _ ‖v‖ UD.mmB _ hAa h1
    have h3 : B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (fun γ => MM.ev v γ e) ‖v‖ :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by show P5.mmUser P0 N ≤ mmB; omega) h2
    refine ⟨h3.1, ⟨_, h3⟩, fun γ hγ hne => ?_⟩
    have hS : γ ∈ UD.S := by
      by_contra hn
      apply hne
      show MM.ev v γ e = 0
      rw [MM.off v γ hγ hn]
      rfl
    exact hSg γ hS
  have hform : ∀ q1 q2, okG m Kc q1 → okG m Kc q2 →
      D.formLev T sg ⟨i, by omega⟩ w
        (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q1) (by rw [ptSize_ptG, hsz]))
        (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q2) (by rw [ptSize_ptG, hsz])) =
      Bf (yG U.betaU m Φ q1) (yG U.betaU m Φ q2) := by
    intro q1 q2 hq1 hq2
    refine (hBfx _ _ _ _ ε'' hε'' (fun e => ?_) (fun e => ?_) (fun e γ hγ => hev_slv q1 hq1 γ hγ e)
      (fun e γ hγ => hev_slv q2 hq2 γ hγ e)).symm
    · exact cccoef_congr (fun γ hγ => hev_slv q1 hq1 γ hγ e) (hcls _ e)
    · exact cccoef_congr (fun γ hγ => hev_slv q2 hq2 γ hγ e) (hcls _ e)
  exact ⟨V, indexVFirst, indexVSecond, hVc, Bf, Φ, Cp, Cst * c, hCp0, hBf, hform, fun t D ht hD => hΦg t D ht hD⟩

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
