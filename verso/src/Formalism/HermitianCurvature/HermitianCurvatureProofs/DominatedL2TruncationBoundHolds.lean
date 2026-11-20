import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFApxDom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFApxDomThQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DominatedL2OperatorBoundHolds

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section general

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `hJ : ∀ H : B.Mat k r → (Wq →L[ℂ] Wp), B.JF D H h = ∫ q, JF.integrand D H h q ∂D.μSS` using `fun H => rfl`. Take `⟨hFi, -⟩` from `Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D A F hT hF`. Take `⟨hGi, -⟩` from `Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D A G hT hG`. Rewrite using `[hJ, hJ, hJ, ← integral_sub (hFi h hh) (hGi h hh)]`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Simplify using `only [JF.integrand, B.rho, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, smul_sub]`.
-/
theorem jf_sub_thr (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hT : JF.TransportedAlt k r A 0) {F G : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : B.InCC A 0 F) (hG : B.InCC A 0 G) {h : B.Mat k r} (hh : h ∈ JF.Om k r D.z D.z') :
    B.JF D (fun g => F g - G g) h = B.JF D F h - B.JF D G h := by
  have hJ : ∀ H : B.Mat k r → (Wq →L[ℂ] Wp), B.JF D H h = ∫ q, JF.integrand D H h q ∂D.μSS := fun H => rfl
  obtain ⟨hFi, -⟩ := Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D A F hT hF
  obtain ⟨hGi, -⟩ := Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D A G hT hG
  rw [hJ, hJ, hJ, ← integral_sub (hFi h hh) (hGi h hh)]
  congr 1
  funext q
  simp only [JF.integrand, B.rho, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, smul_sub]

/- English proof (translation)
Unfold `B.hsVec`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem hsVec_sub'' (A C : Wq →L[ℂ] Wp) : B.hsVec (A - C) = B.hsVec A - B.hsVec C := by
  unfold B.hsVec
  ext i
  simp

end general

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `hG'` using `hG`. Rewrite `hG'` using `[Gp_bigPt_eq]`. Establish `hTT : 0 < TBB.TTp p` using `mul_pos p.T.base.T_pos p.T.base.T'_pos`. Rewrite `hG'` using `[Fin.prod_univ_castSucc c, Complex.normSq_mul]`. Establish `ha0 : 0 ≤ Complex.normSq (∏ i : Fin P.r, c i.castSucc)` using `Complex.normSq_nonneg _`.

Establish `hfac : Complex.normSq (∏ i : Fin P.r, c i.castSucc) * Complex.normSq (c (Fin.last P.r)) - TBB.TTp p * Complex.normSq (∏ i : Fin P.r, c i.castSucc) = Complex.normSq (∏ i : Fin P.r, c i.castSucc) * (Complex.normSq (c (Fin.last P.r)) - TBB.TTp p)` using `by ring`. Rewrite `hG'` using `[hfac]`. Break down `pos_and_pos_or_neg_and_neg_of_mul_pos hG' with ⟨hapos, hb⟩ | ⟨hneg, -⟩` into its components or cases. Use `swap`. Conclude with `absurd ha0 (not_le.mpr hneg)`.

Establish `hne' : ∀ i : Fin P.r, c i.castSucc ≠ 0`. Introduce `i hi`. Apply `hapos.ne'` to reduce the goal to its premises. Rewrite using `[Complex.normSq_eq_zero]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) hi`.

Establish `hlast : c (Fin.last P.r) ≠ 0`. Introduce `h0`. Rewrite `hb` using `[h0, map_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun a => ?_, ⟨hne', ?_⟩⟩` and prove the remaining obligations.

Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact hlast`. Consider the case `cast i => exact hne' i`. Use `show TBB.TTp p < Complex.normSq (c (Fin.last P.r))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pos_bigPt (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) (hG : 0 < TBB.Gp p (TBB.bigPt P.r c)) :
    (∀ a, c a ≠ 0) ∧
      ((fun j => c j.castSucc), c (Fin.last P.r)) ∈ JF.QDom P.k P.r p.T.base.z p.T.base.z' := by
  have hG' := hG
  rw [Gp_bigPt_eq] at hG'
  have hTT : 0 < TBB.TTp p := mul_pos p.T.base.T_pos p.T.base.T'_pos
  rw [Fin.prod_univ_castSucc c, Complex.normSq_mul] at hG'
  have ha0 : 0 ≤ Complex.normSq (∏ i : Fin P.r, c i.castSucc) := Complex.normSq_nonneg _
  have hfac : Complex.normSq (∏ i : Fin P.r, c i.castSucc) * Complex.normSq (c (Fin.last P.r)) -
      TBB.TTp p * Complex.normSq (∏ i : Fin P.r, c i.castSucc)
      = Complex.normSq (∏ i : Fin P.r, c i.castSucc) * (Complex.normSq (c (Fin.last P.r)) - TBB.TTp p) := by ring
  rw [hfac] at hG'
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hG' with ⟨hapos, hb⟩ | ⟨hneg, -⟩
  swap
  · exact absurd ha0 (not_le.mpr hneg)
  have hne' : ∀ i : Fin P.r, c i.castSucc ≠ 0 := by
    intro i hi
    apply hapos.ne'
    rw [Complex.normSq_eq_zero]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hlast : c (Fin.last P.r) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hb
    linarith
  refine ⟨fun a => ?_, ⟨hne', ?_⟩⟩
  · induction a using Fin.lastCases with
    | last => exact hlast
    | cast i => exact hne' i
  · show TBB.TTp p < Complex.normSq (c (Fin.last P.r))
    linarith

/- English proof (translation)
Establish `h1` using `norm_sub_le a b`. Establish `h2 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2`. Use polynomial arithmetic with `[norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 hw]`.
-/
private lemma mul_norm_sub_sq_le_two_mul_add {E : Type*} [SeminormedAddCommGroup E] (w : ℝ) (hw : 0 ≤ w) (a b : E) :
    w * ‖a - b‖ ^ 2 ≤ 2 * (w * ‖a‖ ^ 2) + 2 * (w * ‖b‖ ^ 2) := by
  have h1 := norm_sub_le a b
  have h2 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

/- English proof (translation)
Distinguish the cases in `hG : 0 < TBB.Gp p (TBB.bigPt P.r c)`. Take `⟨hd, hq⟩` from `pos_bigPt p c hG`. Rewrite using `[ew_eq_weight p _ c hd, ew_eq_weight p X c hd, ew_eq_weight p Y c hd]`. Establish `hmem` using `Formalism.FourierDecayAlt.P.big_cell_domain P.k P.r Wp Wq p.T.base _ hq`. Establish `hJ` using `jf_sub_thr p.T.base hT hX hY hmem`.

Simplify using `only [B.gq] at hJ`. Rewrite using `[hJ, hsVec_sub'']`. Conclude with `mul_norm_sub_sq_le_two_mul_add _ (bcWeight_nonneg0 _ _ _ _ _) _ _`. Establish `h0 : ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c))` using `fun h' => hG h'.2`. Rewrite using `[Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p _ h0, Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p X h0, Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p Y h0]`.

Evaluate the numerical expressions.
-/
theorem ew_sub_le (p : KB.Pl P Wp Wq) {A : ℝ} (hT : JF.TransportedAlt P.k P.r A 0) {X Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hX : B.InCC A 0 X) (hY : B.InCC A 0 Y) (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) (fun g => X g - Y g) (P.r + 1) [] (TBB.bigPt P.r c) ≤
      2 * TBB.Ew p (fun _ => 1) X (P.r + 1) [] (TBB.bigPt P.r c) +
        2 * TBB.Ew p (fun _ => 1) Y (P.r + 1) [] (TBB.bigPt P.r c) := by
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · obtain ⟨hd, hq⟩ := pos_bigPt p c hG
    rw [ew_eq_weight p _ c hd, ew_eq_weight p X c hd, ew_eq_weight p Y c hd]
    have hmem := Formalism.FourierDecayAlt.P.big_cell_domain P.k P.r Wp Wq p.T.base _ hq
    have hJ := jf_sub_thr p.T.base hT hX hY hmem
    simp only [B.gq] at hJ
    rw [hJ, hsVec_sub'']
    exact mul_norm_sub_sq_le_two_mul_add _ (bcWeight_nonneg0 _ _ _ _ _) _ _
  · have h0 : ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) := fun h' => hG h'.2
    rw [Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p _ h0, Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p X h0,
      Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p Y h0]
    norm_num

/- English proof (translation)
Distinguish the cases in `hG : 0 < TBB.Gp p (TBB.bigPt P.r c)`. Take `⟨hd, hq⟩` from `pos_bigPt p c hG`. Rewrite using `[ew_eq_weight p F c hd, ew_eq_weight p F' c hd]`. Establish `hmem` using `Formalism.FourierDecayAlt.P.big_cell_domain P.k P.r Wp Wq p.T.base _ hq`. Establish `hJ : B.JF p.T.base F _ = B.JF p.T.base F' _` using `jf_congr_level p.T.base hmem.1 (fun x hx _ => h x hx)`.

Simplify using `only [B.gq] at hJ`. Rewrite using `[hJ]`. Establish `h0 : ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c))` using `fun h' => hG h'.2`. Rewrite using `[Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F h0, Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F' h0]`.
-/
theorem ew_congr_GV (p : KB.Pl P Wp Wq) {F F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV P.k P.r, F g = F' g)
    (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) = TBB.Ew p (fun _ => 1) F' (P.r + 1) [] (TBB.bigPt P.r c) := by
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · obtain ⟨hd, hq⟩ := pos_bigPt p c hG
    rw [ew_eq_weight p F c hd, ew_eq_weight p F' c hd]
    have hmem := Formalism.FourierDecayAlt.P.big_cell_domain P.k P.r Wp Wq p.T.base _ hq
    have hJ : B.JF p.T.base F _ = B.JF p.T.base F' _ := jf_congr_level p.T.base hmem.1 (fun x hx _ => h x hx)
    simp only [B.gq] at hJ
    rw [hJ]
  · have h0 : ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) := fun h' => hG h'.2
    rw [Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F h0, Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F' h0]

/- English proof (translation)
Distinguish the cases in `hγ : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)`. Establish `hE0` using `Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg p Z (TBB.bigPt P.r c)`. Establish `hb` using `nf_pow_bound ‖TBB.Gp p (TBB.bigPt P.r c)‖ (norm_nonneg _) (2 * p₀) N _ hE0`. Establish `heq : TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • Z g) (P.r + 1) [] (TBB.bigPt P.r c) = ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀) * TBB.Ew p (fun _ => 1) Z (P.r + 1) [] (TBB.bigPt P.r c)`. Rewrite using `[Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p _ hγ.1, Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p _ hγ.1, Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow p Z p₀ hγ.1 hγ.2, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq, Real.norm_eq_abs, abs_of_pos hγ.2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `hb`. Rewrite using `[Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p Z hγ, Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p _ hγ]`. Simplify using the standard rewrite rules.
-/
theorem ew_Gpow_le (p : KB.Pl P Wp Wq) (Z : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ N : ℕ) (c : Fin (P.r + 1) → ℂ) :
    ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) * TBB.Ew p (fun _ => 1) Z (P.r + 1) [] (TBB.bigPt P.r c) ≤
      TBB.Ew p (fun _ => 1) Z (P.r + 1) [] (TBB.bigPt P.r c) +
        TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • Z g) (P.r + 1) []
          (TBB.bigPt P.r c) := by
  by_cases hγ : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  · have hE0 := Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg p Z (TBB.bigPt P.r c)
    have hb := nf_pow_bound ‖TBB.Gp p (TBB.bigPt P.r c)‖ (norm_nonneg _) (2 * p₀) N _ hE0
    have heq : TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • Z g)
        (P.r + 1) [] (TBB.bigPt P.r c)
        = ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀) * TBB.Ew p (fun _ => 1) Z (P.r + 1) [] (TBB.bigPt P.r c) := by
      rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p _ hγ.1, Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p _ hγ.1,
        Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow p Z p₀ hγ.1 hγ.2, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq, Real.norm_eq_abs,
        abs_of_pos hγ.2]
      ring
    rw [heq]
    exact hb
  · rw [Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p Z hγ, Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p _ hγ]
    simp

/- English proof (translation)
Take `⟨c0, -, -, hB1, -⟩` from `Formalism.FourierDecayAlt.P.b_any_of_xi P.k P.r Wp Wq p.T.base A hAB`. Take `⟨C, hC⟩` from `hB1`. Use `⟨max C 0, le_max_right _ _, fun H b hH5 hH4 => ?_⟩` and prove the remaining obligations. Take `⟨hfin, -, hbeta⟩` from `hC H H b b hH5 hH5 hH4 hH4`. Use `set w : (Fin P.r → ℂ) × ℂ → ℝ := fun q => bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q with hw`.

Use `set J : (Fin P.r → ℂ) × ℂ → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) := fun q => B.hsVec (B.JF p.T.base H (B.gq p.T.base q)) with hJ`. Establish `hw0 : ∀ q, 0 ≤ w q` using `fun q => bcWeight_nonneg0 _ _ _ _ q`. Establish `hae : (fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c))) =ᵐ[volume] (fun c => ENNReal.ofReal (w (bcE P.r c) * ‖J (bcE P.r c)‖ ^ 2))` using `by filter_upwards [ae_ne_zero_all P.r] with c hc`. Rewrite using `[ew_eq_weight p H c hc, bcE_apply]`. Both sides reduce to the same expression.

Establish `hnorm : ∫⁻ c, ENNReal.ofReal (TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) = B.normSq p.T.base H`. Rewrite using `[lintegral_congr_ae hae]`. Conclude with `(bcE_mp P.r).lintegral_comp_emb (bcE P.r).measurableEmbedding (fun q => ENNReal.ofReal (w q * ‖J q‖ ^ 2))`. Rewrite using `[hnorm]`. Establish `hH0 : B.InCC A 0 H` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono le_rfl (Nat.zero_le 5) hH5`.

Establish `hcont : ContinuousOn (fun q => ‖J q‖ ^ 2) (JF.QDom P.k P.r p.T.base.z p.T.base.z')`. Establish `h1` using `jgq_continuousOn p.T.base hT hH0`. Conclude with `((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.continuous.comp_continuousOn h1).norm).pow 2`. Establish `hmeas : AEStronglyMeasurable (fun q => w q * ‖J q‖ ^ 2) volume`. Establish `h` using `aesm_weight_smul p.T.base hcont`.

Simplify `h` using `only [smul_eq_mul]`. Establish `hint : ∫ q, w q * ‖J q‖ ^ 2 = (B.normSq p.T.base H).toReal` using `integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => mul_nonneg (hw0 q) (sq_nonneg _)) hmeas`. Establish `hbeta' : B.beta p.T.base H H = ((∫ q, w q * ‖J q‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[← integral_complex_ofReal]`. Unfold `B.beta betaBig`.

Use `congr 1`. Use function extensionality and compare the values at `q`. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite `hbeta` using `[hbeta', hint, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[← ENNReal.ofReal_toReal hfin]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_self_nonneg b)`.
-/
theorem ew_lint_le (p : KB.Pl P Wp Wq) {A : ℝ} (hAB : B.AB P.k P.r ≤ A) (hT : JF.TransportedAlt P.k P.r A 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ), B.InCC A 5 H → B.CCle A 4 H b →
      ∫⁻ c, ENNReal.ofReal (TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) ≤ ENNReal.ofReal (C * b * b) := by
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k P.r Wp Wq p.T.base A hAB
  obtain ⟨C, hC⟩ := hB1
  refine ⟨max C 0, le_max_right _ _, fun H b hH5 hH4 => ?_⟩
  obtain ⟨hfin, -, hbeta⟩ := hC H H b b hH5 hH5 hH4 hH4
  set w : (Fin P.r → ℂ) × ℂ → ℝ := fun q => bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q
    with hw
  set J : (Fin P.r → ℂ) × ℂ → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
    fun q => B.hsVec (B.JF p.T.base H (B.gq p.T.base q)) with hJ
  have hw0 : ∀ q, 0 ≤ w q := fun q => bcWeight_nonneg0 _ _ _ _ q

  have hae : (fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)))
      =ᵐ[volume] (fun c => ENNReal.ofReal (w (bcE P.r c) * ‖J (bcE P.r c)‖ ^ 2)) := by
    filter_upwards [ae_ne_zero_all P.r] with c hc
    rw [ew_eq_weight p H c hc, bcE_apply]
    rfl
  have hnorm : ∫⁻ c, ENNReal.ofReal (TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c))
      = B.normSq p.T.base H := by
    rw [lintegral_congr_ae hae]
    exact (bcE_mp P.r).lintegral_comp_emb (bcE P.r).measurableEmbedding
      (fun q => ENNReal.ofReal (w q * ‖J q‖ ^ 2))
  rw [hnorm]

  have hH0 : B.InCC A 0 H := Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono le_rfl (Nat.zero_le 5) hH5
  have hcont : ContinuousOn (fun q => ‖J q‖ ^ 2) (JF.QDom P.k P.r p.T.base.z p.T.base.z') := by
    have h1 := jgq_continuousOn p.T.base hT hH0
    exact ((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.continuous.comp_continuousOn h1).norm).pow 2
  have hmeas : AEStronglyMeasurable (fun q => w q * ‖J q‖ ^ 2) volume := by
    have h := aesm_weight_smul p.T.base hcont
    simpa only [smul_eq_mul] using h
  have hint : ∫ q, w q * ‖J q‖ ^ 2 = (B.normSq p.T.base H).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => mul_nonneg (hw0 q) (sq_nonneg _))
      hmeas
  have hbeta' : B.beta p.T.base H H = ((∫ q, w q * ‖J q‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    unfold B.beta betaBig
    congr 1
    funext q
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hbeta', hint, Complex.norm_real, Real.norm_eq_abs] at hbeta
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  calc (B.normSq p.T.base H).toReal ≤ |(B.normSq p.T.base H).toReal| := le_abs_self _
    _ ≤ C * b * b := hbeta
    _ ≤ max C 0 * b * b := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_self_nonneg b)

end place

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `Cb C₁`. Use `⟨max C₁ 0 + 21, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N hH Th hTh`. Take `⟨-, -, hfck, hf, hA, hN⟩` from `hH`. Take `⟨-, -, hgc, hord⟩` from `hTh`.

Establish `hk : 2 ≤ P.k` using `p.hl.2.2`. Establish `hr0 : (0 : ℝ) ≤ P.r` using `Nat.cast_nonneg _`. Establish `hk2 : (2 : ℝ) ≤ P.k` using `by exact_mod_cast hk`. Establish `hnD : CutMP.nDim P.k P.r = 2 * (P.r : ℝ) + P.k + 1` using `by unfold CutMP.nDim; push_cast; ring`. Rewrite `hgc`, `hord` using `[hnD]`.

Establish `hx1 : 1 ≤ 2 * (P.r : ℝ) + P.k + 1` using `by linarith`. Establish `hR1 : 1 ≤ (P.r : ℝ) + 1` using `by linarith`. Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hC₁ : 0 ≤ C₁`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Establish `hp : 0 < (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1)` using `by positivity`. Establish `h1 : C₁ * (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1) < 0`. Use `mul_neg_of_neg_of_pos h hp` as an intermediate fact. Combine the linear relations using `[this, show C₁ * (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1) = C₁ * ((2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1)) by ring]`.

Establish `h2 : (0 : ℝ) ≤ (B.opOrder Th : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd0 : 0 ≤ C₁ * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1)` using `by positivity`. Take `⟨-, hcc1⟩` from `Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds P.k P.r Wp Wq Th _ A₀ hd0 hgc f hfck hf`. Establish `hcc2` using `inCC_Gpow_smul p.T.base.z p.T.base.z' p₀ hcc1`.

Take `⟨bf, hbf⟩` from `hf (5 + B.opOrder Th)`. Establish `hbf0 : 0 ≤ bf` using `JCx2.pd_ccle_nonneg hbf`. Take `⟨Kp, hKp0, hKp⟩` from `JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) (5 + B.opOrder Th)`. Take `⟨KT, hKT0, hKT⟩` from `jdCCLowerQ Th _ (A₀ - 1) hd0 hgc 5`. Use `set d : ℝ := C₁ * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1) with hd`.

Use `set q₀ : ℝ := (((2 * P.r + 2) * p₀ : ℕ) : ℝ) with hq₀`. Establish `hq0 : 0 ≤ q₀` using `Nat.cast_nonneg _`. Use `set x : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hx`. Use `set R : ℝ := (P.r : ℝ) + 1 with hR`. Establish `hS : 0 ≤ R ^ 4 * (N * x ^ 2 + x ^ 3)` using `by positivity`.

Establish `hbig : (C₁ + 21) * (R ^ 4 * (N * x ^ 2 + x ^ 3)) ≤ A₀ - q₀`. Establish `hA' : (max C₁ 0 + 21) * (R ^ 4 * (N * x ^ 2 + x ^ 3)) ≤ A₀ - q₀`. Rewrite using `[← mul_assoc]`. Conclude with `hA`. Conclude with `le_trans (mul_le_mul_of_nonneg_right (by linarith [le_max_left C₁ 0]) hS) hA'`.

Establish `hdle` using `nf_arith_d C₁ R x N hC₁ hR1 hx1 hN0`. Establish `hlow0` using `nf_arith_low R x N hR1 hx1 hN0`. Establish `hx3 : 1 ≤ x ^ 3` using `one_le_pow₀ hx1`. Establish `hRx : 1 ≤ R * x ^ 3` using `by nlinarith`. Use `set A₃ : ℝ := A₀ - q₀ - d - 1 with hA₃`.

Establish `hlow : 20 * (R * x ^ 3) ≤ A₃`. Establish `e : (C₁ + 21) * (R ^ 4 * (N * x ^ 2 + x ^ 3)) = C₁ * (R ^ 4 * (N * x ^ 2 + x ^ 3)) + 21 * (R ^ 4 * (N * x ^ 2 + x ^ 3))` using `by ring`. Establish `hdd : d = C₁ * R * x * (N + 1)` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hab` using `nf_arith_ab (P.r : ℝ) (P.k : ℝ) hr0 hk2`.

Establish `hthr` using `nf_arith_thr R x hR1 hx1`. Establish `hAB_le : ∀ A : ℝ, A₃ ≤ A → B.AB P.k P.r ≤ A`. Introduce `A hA2`. Unfold `B.AB`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hThr : ∀ A : ℝ, A₃ ≤ A → JF.TransportedAlt P.k P.r A 0`. Introduce `A hA2`. Unfold `JF.TransportedAlt`. Rewrite using `[lt_div_iff₀ (by positivity)]`. Establish `e : (((2 * P.r + P.k + 1 : ℕ) : ℝ)) = x` using `by simp only [hx]; push_cast; ring`.

Rewrite using `[e]`. Simplify using `only [Nat.cast_zero, mul_zero, sub_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA3le : A₃ ≤ A₀ - 1 - d` using `by linarith`. Establish `hA3X : A₃ ≤ A₀ - d` using `by linarith`.

Establish `hA3X' : A₃ ≤ A₀ - d - q₀` using `by linarith`. Use `set ψ : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun m g => JCx2.pdPsi ((m : ℝ) + 1) g • f g with hψ`. Establish `hψc : ∀ m : ℕ, B.CCle (A₀ - 1) (5 + B.opOrder Th) (ψ m) (Kp * bf / ((m : ℝ) + 1))` using `fun m => hKp _ (by positivity) A₀ f bf hbf`. Establish `hψs : ∀ m : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (ψ m)` using `fun m => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hfck`. Establish `hYc : ∀ m : ℕ, B.CCle (A₀ - 1 - d) 5 (B.opApply Th (ψ m)) (KT * (Kp * bf / ((m : ℝ) + 1)))` using `fun m => hKT (ψ m) _ (hψs m) (hψc m)`.

Take `⟨KG, hKG0, hKG⟩` from `(pd_good_Gpow (Wp := Wp) (Wq := Wq) p.T.base.z p.T.base.z' p₀).2 A₃ 5`. Establish `e3 : A₃ + q₀ = A₀ - 1 - d` using `by rw [hA₃]; ring`. Establish `hY'c : ∀ m : ℕ, B.CCle A₃ 5 (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th (ψ m) g) (KG * (KT * (Kp * bf / ((m : ℝ) + 1))))`. Introduce `m`. Establish `h1` using `hYc m`.

Rewrite `h1` using `[← e3]`. Conclude with `hKG _ _ h1`. Take `⟨C3, hC30, hC3⟩` from `ew_lint_le p (hAB_le A₃ le_rfl) (hThr A₃ le_rfl)`. Establish `aeE : ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), A₃ ≤ A → (∀ j : ℕ, j ≤ 5 → B.InCC A j H) → AEMeasurable (fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)))` using `fun H A hA hH => (ew_integrable p (hAB_le A hA) (hThr A hA) hH).aestronglyMeasurable.aemeasurable.ennreal_ofReal`. Establish `intX` using `ew_integrable p (hAB_le _ hA3X) (hThr _ hA3X) (fun j _ => hcc1 j)`.

Establish `intX'` using `ew_integrable p (hAB_le _ hA3X') (hThr _ hA3X') (fun j _ => hcc2 j)`. Establish `aeX` using `intX.aestronglyMeasurable.aemeasurable.ennreal_ofReal`. Establish `aeX'` using `intX'.aestronglyMeasurable.aemeasurable.ennreal_ofReal`. Establish `aeY : ∀ m : ℕ, AEMeasurable (fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (B.opApply Th (ψ m)) (P.r + 1) [] (TBB.bigPt P.r c)))` using `fun m => aeE _ A₃ le_rfl fun j hj => ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA3le (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hj (hYc m))⟩`. Establish `aeY' : ∀ m : ℕ, AEMeasurable (fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th (ψ m) g) (P.r + 1) [] (TBB.bigPt P.r c)))` using `fun m => aeE _ A₃ le_rfl fun j hj => ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hj (hY'c m)⟩`.

Use `set T : ℕ → (Fin (P.r + 1) → ℂ) → ℝ≥0∞ := fun m c => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (B.opApply Th (ψ m)) (P.r + 1) [] (TBB.bigPt P.r c)) + ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th (ψ m) g) (P.r + 1) …`. Establish `aeT : ∀ m, AEMeasurable (T m)` using `fun m => (aeY m).add (aeY' m)`. Use `set a : ℝ := KT * (Kp * bf) with ha`. Use `set M : ℝ := C3 * a ^ 2 + C3 * KG ^ 2 * a ^ 2 with hM`. Establish `hM0 : 0 ≤ M` using `by positivity`.

Establish `hT_le : ∀ m : ℕ, ∫⁻ c, T m c ≤ ENNReal.ofReal (M * (1 / ((m : ℝ) + 1) ^ 2))`. Introduce `m`. Establish `hm1 : (0 : ℝ) < (m : ℝ) + 1` using `by positivity`. Establish `i1` using `hC3 (B.opApply Th (ψ m)) _ ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA3le (hYc m)⟩ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA3le (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by norm_num) (hYc m)))`. Establish `i2` using `hC3 _ _ ⟨_, hY'c m⟩ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by norm_num) (hY'c m))`.

Rewrite using `[hTdef]`. Simplify using `only`. Rewrite using `[lintegral_add_right' _ (aeY' m)]`. Use `le_trans (add_le_add i1 i2) ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_add (by positivity) (by positivity)]`.

Apply `le_of_eq` to reduce the goal to its premises. Use `congr 1`. Rewrite using `[hM, ha]`. Clear the denominators using the available nonvanishing facts. Establish `hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2)`.

Use `(summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)` as an intermediate fact. Simplify using `using this`. Use `set Hn : (Fin (P.r + 1) → ℂ) → ℝ≥0∞ := fun c => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c)) + ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th f g) (P.r + 1) [] (TBB.bigP …`. Establish `aeHn : AEMeasurable Hn` using `(aeX.add aeX').add (AEMeasurable.tsum aeT)`. Establish `hfin : ∫⁻ c, Hn c ≠ ∞`.

Rewrite using `[hHn]`. Simplify using `only`. Rewrite using `[lintegral_add_right' _ (AEMeasurable.tsum aeT), lintegral_tsum aeT, lintegral_add_right' _ aeX']`. Use `ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨intX.lintegral_lt_top.ne, intX'.lintegral_lt_top.ne⟩, ?_⟩` and prove the remaining obligations. Use `ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hT_le)` and prove the remaining obligations.

Rewrite using `[← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg hM0 (by positivity)) (hs.mul_left M)]`. Conclude with `ENNReal.ofReal_ne_top`. Use `⟨fun c => 2 * (Hn c).toReal, (integrable_toReal_of_lintegral_ne_top aeHn hfin).const_mul 2, fun n => ?_⟩` and prove the remaining obligations. Use `filter_upwards [ae_lt_top' aeHn hfin] with c hc`. Establish `hfn : ∀ g ∈ B.GV P.k P.r, B.opApply Th (fun g => cutN P.k P.r n g • f g) g = B.opApply Th f g - B.opApply Th (ψ n) g`.

Introduce `g hg`. Establish `e : (fun g => cutN P.k P.r n g • f g) = fun g => f g - ψ n g`. Use function extensionality and compare the values at `g'`. Rewrite using `[PBE.cut_eq (fun n g => cutN P.k P.r n g) (fun n g => rfl) n g']`. Simplify using `only [hψ, sub_smul, one_smul]`.

Rewrite using `[e]`. Conclude with `PBE.opApply_sub Th hfck (hψs n) g hg`. Rewrite using `[ew_congr_GV p hfn c]`. Establish `hX0 : B.InCC A₃ 0 (B.opApply Th f)` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono hA3X le_rfl (hcc1 0)`. Establish `hY0 : B.InCC A₃ 0 (B.opApply Th (ψ n))` using `⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA3le (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (Nat.zero_le 5) (hYc n))⟩`.

Establish `hXY` using `ew_sub_le p (hThr A₃ le_rfl) hX0 hY0 c`. Establish `gX` using `ew_Gpow_le p (B.opApply Th f) p₀ N c`. Establish `gY` using `ew_Gpow_le p (B.opApply Th (ψ n)) p₀ N c`. Establish `n1` using `TBBx4.ew_nonneg p (B.opApply Th f) (TBB.bigPt P.r c)`. Establish `n2` using `TBBx4.ew_nonneg p (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th f g) (TBB.bigPt P.r c)`.

Establish `n3` using `TBBx4.ew_nonneg p (B.opApply Th (ψ n)) (TBB.bigPt P.r c)`. Establish `n4` using `TBBx4.ew_nonneg p (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th (ψ n) g) (TBB.bigPt P.r c)`. Establish `hGn : 0 ≤ ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N)` using `by positivity`. Establish `hle : ENNReal.ofReal (TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c) + TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th f g) (P.r + 1) [] (TBB.bigPt P.r c) + (TBB.Ew p (fun _ => 1) (B.opApply Th (ψ n)) (P.r …`. Rewrite using `[ENNReal.ofReal_add (add_nonneg n1 n2) (add_nonneg n3 n4), ENNReal.ofReal_add n1 n2, ENNReal.ofReal_add n3 n4, hHn]`.

Conclude with `add_le_add le_rfl (ENNReal.le_tsum (f := fun m => T m c) n)`. Establish `hle'` using `ENNReal.toReal_mono hc.ne hle`. Rewrite `hle'` using `[ENNReal.toReal_ofReal (add_nonneg (add_nonneg n1 n2) (add_nonneg n3 n4))]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dominated_L2_truncation_bound_holds : DominatedL2TruncationBound := by
  intro Cb C₁
  refine ⟨max C₁ 0 + 21, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N hH Th hTh
  obtain ⟨-, -, hfck, hf, hA, hN⟩ := hH
  obtain ⟨-, -, hgc, hord⟩ := hTh
  have hk : 2 ≤ P.k := p.hl.2.2
  have hr0 : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hk2 : (2 : ℝ) ≤ P.k := by exact_mod_cast hk
  have hnD : CutMP.nDim P.k P.r = 2 * (P.r : ℝ) + P.k + 1 := by unfold CutMP.nDim; push_cast; ring
  rw [hnD] at hgc hord
  have hx1 : 1 ≤ 2 * (P.r : ℝ) + P.k + 1 := by linarith
  have hR1 : 1 ≤ (P.r : ℝ) + 1 := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hC₁ : 0 ≤ C₁ := by
    by_contra h
    push Not at h
    have hp : 0 < (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1) := by positivity
    have h1 : C₁ * (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1) < 0 := by
      have := mul_neg_of_neg_of_pos h hp
      linarith [this, show C₁ * (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1) =
        C₁ * ((2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1)) by ring]
    have h2 : (0 : ℝ) ≤ (B.opOrder Th : ℝ) := Nat.cast_nonneg _
    linarith
  have hd0 : 0 ≤ C₁ * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1) := by positivity
  obtain ⟨-, hcc1⟩ := Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds P.k P.r Wp Wq Th _ A₀ hd0 hgc f hfck hf
  have hcc2 := inCC_Gpow_smul p.T.base.z p.T.base.z' p₀ hcc1
  obtain ⟨bf, hbf⟩ := hf (5 + B.opOrder Th)
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) (5 + B.opOrder Th)
  obtain ⟨KT, hKT0, hKT⟩ := jdCCLowerQ Th _ (A₀ - 1) hd0 hgc 5
  set d : ℝ := C₁ * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1) * ((N : ℝ) + 1) with hd
  set q₀ : ℝ := (((2 * P.r + 2) * p₀ : ℕ) : ℝ) with hq₀
  have hq0 : 0 ≤ q₀ := Nat.cast_nonneg _
  set x : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hx
  set R : ℝ := (P.r : ℝ) + 1 with hR
  have hS : 0 ≤ R ^ 4 * (N * x ^ 2 + x ^ 3) := by positivity
  have hbig : (C₁ + 21) * (R ^ 4 * (N * x ^ 2 + x ^ 3)) ≤ A₀ - q₀ := by
    have hA' : (max C₁ 0 + 21) * (R ^ 4 * (N * x ^ 2 + x ^ 3)) ≤ A₀ - q₀ := by
      rw [← mul_assoc]; exact hA
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith [le_max_left C₁ 0]) hS) hA'
  have hdle := nf_arith_d C₁ R x N hC₁ hR1 hx1 hN0
  have hlow0 := nf_arith_low R x N hR1 hx1 hN0
  have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx1
  have hRx : 1 ≤ R * x ^ 3 := by nlinarith
  set A₃ : ℝ := A₀ - q₀ - d - 1 with hA₃
  have hlow : 20 * (R * x ^ 3) ≤ A₃ := by
    have e : (C₁ + 21) * (R ^ 4 * (N * x ^ 2 + x ^ 3)) =
        C₁ * (R ^ 4 * (N * x ^ 2 + x ^ 3)) + 21 * (R ^ 4 * (N * x ^ 2 + x ^ 3)) := by ring
    have hdd : d = C₁ * R * x * (N + 1) := rfl
    linarith
  have hab := nf_arith_ab (P.r : ℝ) (P.k : ℝ) hr0 hk2
  have hthr := nf_arith_thr R x hR1 hx1
  have hAB_le : ∀ A : ℝ, A₃ ≤ A → B.AB P.k P.r ≤ A := by
    intro A hA2
    unfold B.AB
    linarith
  have hThr : ∀ A : ℝ, A₃ ≤ A → JF.TransportedAlt P.k P.r A 0 := by
    intro A hA2
    unfold JF.TransportedAlt
    rw [lt_div_iff₀ (by positivity)]
    have e : (((2 * P.r + P.k + 1 : ℕ) : ℝ)) = x := by simp only [hx]; push_cast; ring
    rw [e]
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    linarith
  have hA3le : A₃ ≤ A₀ - 1 - d := by linarith
  have hA3X : A₃ ≤ A₀ - d := by linarith
  have hA3X' : A₃ ≤ A₀ - d - q₀ := by linarith

  set ψ : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun m g => JCx2.pdPsi ((m : ℝ) + 1) g • f g with hψ
  have hψc : ∀ m : ℕ, B.CCle (A₀ - 1) (5 + B.opOrder Th) (ψ m) (Kp * bf / ((m : ℝ) + 1)) := fun m =>
    hKp _ (by positivity) A₀ f bf hbf
  have hψs : ∀ m : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (ψ m) := fun m => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hfck
  have hYc : ∀ m : ℕ, B.CCle (A₀ - 1 - d) 5 (B.opApply Th (ψ m)) (KT * (Kp * bf / ((m : ℝ) + 1))) := fun m =>
    hKT (ψ m) _ (hψs m) (hψc m)
  obtain ⟨KG, hKG0, hKG⟩ := (pd_good_Gpow (Wp := Wp) (Wq := Wq) p.T.base.z p.T.base.z' p₀).2 A₃ 5
  have e3 : A₃ + q₀ = A₀ - 1 - d := by rw [hA₃]; ring
  have hY'c : ∀ m : ℕ, B.CCle A₃ 5 (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) •
      B.opApply Th (ψ m) g) (KG * (KT * (Kp * bf / ((m : ℝ) + 1)))) := by
    intro m
    have h1 := hYc m
    rw [← e3] at h1
    exact hKG _ _ h1
  obtain ⟨C3, hC30, hC3⟩ := ew_lint_le p (hAB_le A₃ le_rfl) (hThr A₃ le_rfl)

  have aeE : ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), A₃ ≤ A → (∀ j : ℕ, j ≤ 5 → B.InCC A j H) →
      AEMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c))) :=
    fun H A hA hH => (ew_integrable p (hAB_le A hA) (hThr A hA) hH).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have intX := ew_integrable p (hAB_le _ hA3X) (hThr _ hA3X) (fun j _ => hcc1 j)
  have intX' := ew_integrable p (hAB_le _ hA3X') (hThr _ hA3X') (fun j _ => hcc2 j)
  have aeX := intX.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have aeX' := intX'.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have aeY : ∀ m : ℕ, AEMeasurable (fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (B.opApply Th (ψ m)) (P.r + 1) [] (TBB.bigPt P.r c))) := fun m =>
    aeE _ A₃ le_rfl fun j hj => ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA3le (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hj (hYc m))⟩
  have aeY' : ∀ m : ℕ, AEMeasurable (fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) •
        B.opApply Th (ψ m) g) (P.r + 1) [] (TBB.bigPt P.r c))) := fun m =>
    aeE _ A₃ le_rfl fun j hj => ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hj (hY'c m)⟩
  set T : ℕ → (Fin (P.r + 1) → ℂ) → ℝ≥0∞ := fun m c =>
    ENNReal.ofReal (TBB.Ew p (fun _ => 1) (B.opApply Th (ψ m)) (P.r + 1) [] (TBB.bigPt P.r c)) +
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) •
        B.opApply Th (ψ m) g) (P.r + 1) [] (TBB.bigPt P.r c)) with hTdef
  have aeT : ∀ m, AEMeasurable (T m) := fun m => (aeY m).add (aeY' m)

  set a : ℝ := KT * (Kp * bf) with ha
  set M : ℝ := C3 * a ^ 2 + C3 * KG ^ 2 * a ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hT_le : ∀ m : ℕ, ∫⁻ c, T m c ≤ ENNReal.ofReal (M * (1 / ((m : ℝ) + 1) ^ 2)) := by
    intro m
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have i1 := hC3 (B.opApply Th (ψ m)) _ ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA3le (hYc m)⟩
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA3le (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by norm_num) (hYc m)))
    have i2 := hC3 _ _ ⟨_, hY'c m⟩ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by norm_num) (hY'c m))
    rw [hTdef]
    simp only
    rw [lintegral_add_right' _ (aeY' m)]
    refine le_trans (add_le_add i1 i2) ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply le_of_eq
    congr 1
    rw [hM, ha]
    field_simp
  have hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  set Hn : (Fin (P.r + 1) → ℂ) → ℝ≥0∞ := fun c =>
    ENNReal.ofReal (TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c)) +
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) •
        B.opApply Th f g) (P.r + 1) [] (TBB.bigPt P.r c)) + ∑' m, T m c with hHn
  have aeHn : AEMeasurable Hn := (aeX.add aeX').add (AEMeasurable.tsum aeT)
  have hfin : ∫⁻ c, Hn c ≠ ∞ := by
    rw [hHn]
    simp only
    rw [lintegral_add_right' _ (AEMeasurable.tsum aeT), lintegral_tsum aeT, lintegral_add_right' _ aeX']
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨intX.lintegral_lt_top.ne, intX'.lintegral_lt_top.ne⟩, ?_⟩
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hT_le)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg hM0 (by positivity)) (hs.mul_left M)]
    exact ENNReal.ofReal_ne_top
  refine ⟨fun c => 2 * (Hn c).toReal, (integrable_toReal_of_lintegral_ne_top aeHn hfin).const_mul 2, fun n => ?_⟩
  filter_upwards [ae_lt_top' aeHn hfin] with c hc
  have hfn : ∀ g ∈ B.GV P.k P.r, B.opApply Th (fun g => cutN P.k P.r n g • f g) g =
      B.opApply Th f g - B.opApply Th (ψ n) g := by
    intro g hg
    have e : (fun g => cutN P.k P.r n g • f g) = fun g => f g - ψ n g := by
      funext g'
      rw [PBE.cut_eq (fun n g => cutN P.k P.r n g) (fun n g => rfl) n g']
      simp only [hψ, sub_smul, one_smul]
    rw [e]
    exact PBE.opApply_sub Th hfck (hψs n) g hg
  rw [ew_congr_GV p hfn c]
  have hX0 : B.InCC A₃ 0 (B.opApply Th f) := Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono hA3X le_rfl (hcc1 0)
  have hY0 : B.InCC A₃ 0 (B.opApply Th (ψ n)) :=
    ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hA3le (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (Nat.zero_le 5) (hYc n))⟩
  have hXY := ew_sub_le p (hThr A₃ le_rfl) hX0 hY0 c
  have gX := ew_Gpow_le p (B.opApply Th f) p₀ N c
  have gY := ew_Gpow_le p (B.opApply Th (ψ n)) p₀ N c
  have n1 := TBBx4.ew_nonneg p (B.opApply Th f) (TBB.bigPt P.r c)
  have n2 := TBBx4.ew_nonneg p (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th f g)
    (TBB.bigPt P.r c)
  have n3 := TBBx4.ew_nonneg p (B.opApply Th (ψ n)) (TBB.bigPt P.r c)
  have n4 := TBBx4.ew_nonneg p (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) •
    B.opApply Th (ψ n) g) (TBB.bigPt P.r c)
  have hGn : 0 ≤ ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) := by positivity
  have hle : ENNReal.ofReal (TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c) +
      TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Th f g)
        (P.r + 1) [] (TBB.bigPt P.r c) +
      (TBB.Ew p (fun _ => 1) (B.opApply Th (ψ n)) (P.r + 1) [] (TBB.bigPt P.r c) +
        TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) •
          B.opApply Th (ψ n) g) (P.r + 1) [] (TBB.bigPt P.r c))) ≤ Hn c := by
    rw [ENNReal.ofReal_add (add_nonneg n1 n2) (add_nonneg n3 n4), ENNReal.ofReal_add n1 n2,
      ENNReal.ofReal_add n3 n4, hHn]
    exact add_le_add le_rfl (ENNReal.le_tsum (f := fun m => T m c) n)
  have hle' := ENNReal.toReal_mono hc.ne hle
  rw [ENNReal.toReal_ofReal (add_nonneg (add_nonneg n1 n2) (add_nonneg n3 n4))] at hle'
  calc ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
        TBB.Ew p (fun _ => 1) (fun g => B.opApply Th f g - B.opApply Th (ψ n) g) (P.r + 1) [] (TBB.bigPt P.r c)
      ≤ ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
        (2 * TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c) +
          2 * TBB.Ew p (fun _ => 1) (B.opApply Th (ψ n)) (P.r + 1) [] (TBB.bigPt P.r c)) :=
        mul_le_mul_of_nonneg_left hXY hGn
    _ = 2 * (‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
          TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c)) +
        2 * (‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
          TBB.Ew p (fun _ => 1) (B.opApply Th (ψ n)) (P.r + 1) [] (TBB.bigPt P.r c)) := by ring
    _ ≤ 2 * (Hn c).toReal := by linarith

/- English proof (translation)
The claim follows from `nfApxDomAll_of_cut domination_at_zero_holds hP dominated_L2_truncation_bound_holds`.
-/
theorem nfApxDomAll_of_ptw (hP : NFDomPtw) : NFApxDomAll := nfApxDomAll_of_cut domination_at_zero_holds hP dominated_L2_truncation_bound_holds

end

end Formalism.FourierDecayAlt.P.CutBP
