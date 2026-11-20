import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBDisc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerCmLogPeriodEqConst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralLevelMulKappa
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.IntCuspLat

/- English proof (translation)
Take `⟨-, -, -, hx0, hx1, -⟩` from `GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins`. Establish `habs` using `h.xiAbs j hj σ hσ k`. Establish `hperf` using `GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ)) k`. Establish `hξ` using `GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀ (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((T.U j σ).X k).ξ0_im (habs _).symm`. Establish `hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((T.U j σ).X k).ξ0 * D.host.AA * D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1`.

Establish `h1` using `Formalism.IndefR.Fin.factPrincipalDatum D.R D.host`. Break down `hξ with e | e` into its components or cases. Rewrite using `[e]`. Conclude with `h1`. Rewrite using `[e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp, ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]`.

Conclude with `h1`. Establish `hM : 0 < T.Q.l.M` using `by have := T.Q.l.three_le; omega`. Take `⟨Xx, h1, h2, h3⟩` from `GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((T.U j σ).X k) D.host.AA D.host.AAbar (xiR D) T.Q.l.M (fun a => by`. Rewrite using `[GlobalTheory.LatticeData.cc_eq_conj]`. Conclude with `⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)`.

Use `hone habs hx1 hperf.1 hperf.2 hM (fun γ => gamAt_of_lawsM D T h j hj σ hσ k γ)`. Conclude with `⟨{ Xx with k0 := 2 * xiR D minWeight_pos := by positivity k0_le := by linarith ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((T.U j σ).X k).ξ0 from congrArg _ h1, habs]; ring }, h1, h2, h3, rfl⟩`.
-/
theorem exists_dataX (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) :
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D := by
  obtain ⟨-, -, -, hx0, hx1, -⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have habs := h.xiAbs j hj σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
    (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((T.U j σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((T.U j σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hM : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((T.U j σ).X k) D.host.AA D.host.AAbar
    (xiR D) T.Q.l.M
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (fun γ => gamAt_of_lawsM D T h j hj σ hσ k γ)
  exact ⟨{ Xx with
    k0 := 2 * xiR D
    minWeight_pos := by positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((T.U j σ).X k).ξ0 from congrArg _ h1, habs]; ring }, h1, h2, h3, rfl⟩

/- English proof (translation)
Take `⟨C0, hC0, hroom⟩` from `GlobalTheory.room_of_constants`. Establish `hr : 0 < D.R.r`. Use `D.R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.

Establish `hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r` using `(h.unf j hj T.σ₀ T.good_σ₀).1.symm`. Establish `hf` using `GlobalTheory.WtSizes.fdeg_eq D`. Establish `hd1` using `GlobalTheory.WtSizes.one_le_dE D`. Establish `hts` using `GlobalTheory.WtSizes.tot_le_size w`. Establish `hwf : ∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size` using `fun k => by`.

Use `(Finset.sum_le_sum fun τ _ => GlobalTheory.WtSizes.spread_laU_le T hr w k τ).trans (le_trans ?_ hts)` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib]`. Use `add_le_add ?_ ?_` and prove the remaining obligations. Conclude with `GlobalTheory.WtSizes.sum_cm_le ((T.U j T.σ₀).X k) (GlobalTheory.WtSizes.tot w)` after adjusting the coercions. Rewrite using `[Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), hf, nsmul_eq_mul]`.

Use `mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)` and prove the remaining obligations. Conclude with `Nat.le_mul_of_pos_right _ hr` after adjusting the coercions. Establish `hsz : ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size`. Use `le_trans (add_le_add ?_ le_rfl) hts` and prove the remaining obligations. Conclude with `Finset.sum_le_sum fun b _ => GlobalTheory.WtSizes.sum_wtA_le_tot w b _` after adjusting the coercions.

Use `haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩`. Use `haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩`. Establish `hd4 : D.host.d % 4 = 3`. Use `T.Q.H.d_mod` as an intermediate fact. Rewrite `this` using `[h.pins.1.1]`.

Use linear arithmetic over natural numbers and integers. Take `⟨_, χ, hχ, -⟩` from `GlobalTheory.LamF.exists_kronecker_logOm_re D.host.E h.pins.1.1 hd4`. Establish `g0` using `(D.host.g_prime 0).pos`. Establish `g1` using `(D.host.g_prime 1).pos`. Establish `hdpos : 0 < D.host.d` using `lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2`.

Establish `hN : 0 < Ideal.absNorm D.host.ccK` using `Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Take `⟨M, hMdef⟩ : ∃ M : ℝ, M = ((D.host.g 0 * D.host.g 1 * (Ideal.absNorm D.host.ccK * D.host.d) : ℕ) : ℝ)` from `⟨_, rfl⟩`. Establish `hM : (0 : ℝ) < M`. Rewrite using `[hMdef]`. Conclude with `Nat.mul_pos (Nat.mul_pos g0 g1) (Nat.mul_pos hN hdpos)` after adjusting the coercions.

Use `⟨(C0 * ((fdeg D.host.E : ℝ) * D.R.r + |Real.log (M * (2 * xiR D))| + Real.log (dE D.host.E) + |(GlobalTheory.CM.logOm D.host.E χ).re|) ^ (2 : ℝ) * (1 + Real.log w.size) * w.size) * (Module.finrank ℚ T.Q.c.F : ℝ), fun F hFC hF hF1 => ?_⟩` and prove the remaining obligations. Establish `hhol : rdU (T.U j T.σ₀) F ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)` using `((mem_cusp _ _ _ _ _ F).1 hFC).2 T.σ₀ T.good_σ₀`. Establish `hSS` using `Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) hhol`. Establish `hfin : supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) ≠ ⊤` using `supE_cusp_ne_top T.good_σ₀ hFC`. Establish `hpos : 0 < supN (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F)`.

Break down `(ENNReal.toReal_nonneg : 0 ≤ (supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F)).toReal).lt_or_eq with hlt | heq` into its components or cases. Conclude with `hlt`. Conclude with `absurd (h.supDef j hj (wtA w) w.n (dom_wtA w) T.σ₀ T.good_σ₀ F hFC heq.symm) hF1`. Take `⟨k, z0, hz0, hlt⟩` from `Formalism.L2.Pj.abelian₂.half_max (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) hpos hfin`. Establish `hhalf : ∀ x ∈ ((T.U j T.σ₀).X k).dom, ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) x ≤ 2 * ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0` using `fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le`.

Establish `hposz : 0 < ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨Xx, hX, hXg, hΛ, hk0⟩` from `exists_dataX D T h j hj T.σ₀ T.good_σ₀ k`. Establish `habs : ∀ τ : D.host.E →+* ℂ, ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d)` using `fun τ => by`. Rewrite using `[← GlobalTheory.TransvModel.xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]`.

Establish `htr : ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((M : ℂ) * τ.1 b)`. Rewrite using `[← hX]`. Introduce `v hv hiso b hb hbi`. Use `GlobalTheory.TransvModel.transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d) (GlobalTheory.TransvModel.isIntegral_level_mul_kappa Xx.toData hN hdpos D.host.φ₀ (habs _)) v hv hiso b hb hbi` as an intermediate fact. Rewrite `this` using `[hXg.trans h.pins.2.1.1, ← hMdef]`. Then use the resulting hypothesis.

Take `⟨x, lam, hx, hLB, hPx⟩` from `Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((T.U j T.σ₀).X k) hX _ _ z0 M w.size (hSS k) hM (hwf k) w.one_le_size hr (fun v hv hvv b hb hbi => by`. Take `⟨γ, hγ, hγ'⟩` from `htr v hv hvv b hb hbi`. Conclude with `⟨γ, hγ, h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA w) k γ hγ, hγ'⟩) hz0 hhalf hposz`. Establish `hf1 : 1 ≤ fdeg D.host.E`. Establish `h2` using `finrank_eq_two_mul_half_degree (E := D.host.E)`.

Establish `h3 : 0 < Module.finrank ℚ D.host.E` using `Module.finrank_pos`. Establish `h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Establish `hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * (2 * xiR D))| + 3 + Real.log (dE D.host.E)`. Rewrite using `[hk0]`.

Use `le_abs_self (Real.log (M * (2 * xiR D)))` as an intermediate fact. Use `abs_nonneg (Real.log (M * (2 * xiR D)))` as an intermediate fact. Use `Real.log_nonneg hd1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hLa1, hr'⟩` from `hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) _ (GlobalTheory.CM.logOm D.host.E χ).re M Xx.k0 w.size hf1 hr Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos w.one_le_size hlog`.

Establish `hr''` using `hr' _ _ (Nat.cast_nonneg _) (by positivity) hsz C0 2 le_rfl le_rfl`. Establish `hNs : ∀ σ, IsNormOn (T.C j w) σ (T.Ns j w σ)` using `fun σ => (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf`. Establish `hSpos : ∀ σ, 0 < supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n F` using `fun σ => lt_of_le_of_ne ((hNs σ).nonneg F hFC) fun h0 => hF1 ((hNs σ).defin F hFC h0.symm)`. Establish `h5` using `GlobalTheory.LamT.meanLogSup_lowerBound D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D) (h.unf j hj) (h.xiAbs j hj) (by rw [hpq]; exact hr) χ hχ (wtA w) w.n (dom_wtA w) F hFC hF hSpos k ⟨x, hx⟩ Xx hX D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalD …`. Establish `hf' : Module.finrank ℚ D.host.E / 2 = D.R.f` using `hf`.

Rewrite `h5` using `[hf']`. Establish `hK : (0 : ℝ) < Module.finrank ℚ T.Q.c.F` using `by exact_mod_cast Module.finrank_pos`. Rewrite using `[← neg_mul, ← le_div_iff₀ hK]`. Use `le_trans ?_ h5` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_lowerBound (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) :
    ∃ B : ℝ, ∀ F ∈ T.C j w, (∀ la, ∀ v ∈ T.Vs j la, 0 ≤ v F) → F ≠ 0 →
      -B ≤ ∑ σ : T.Q.c.F →+* ℂ, Real.log (T.Ns j w σ F) := by
  classical
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.room_of_constants
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := (h.unf j hj T.σ₀ T.good_σ₀).1.symm
  have hf := GlobalTheory.WtSizes.fdeg_eq D
  have hd1 := GlobalTheory.WtSizes.one_le_dE D
  have hts := GlobalTheory.WtSizes.tot_le_size w
  have hwf : ∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size := fun k => by
    refine (Finset.sum_le_sum fun τ _ => GlobalTheory.WtSizes.spread_laU_le T hr w k τ).trans (le_trans ?_ hts)
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact_mod_cast GlobalTheory.WtSizes.sum_cm_le ((T.U j T.σ₀).X k) (GlobalTheory.WtSizes.tot w)
    · rw [Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), hf, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_mul_of_pos_right _ hr
  have hsz : ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) +
      ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
    refine le_trans (add_le_add ?_ le_rfl) hts
    exact_mod_cast Finset.sum_le_sum fun b _ => GlobalTheory.WtSizes.sum_wtA_le_tot w b _
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd4 : D.host.d % 4 = 3 := by
    have := T.Q.H.d_mod
    rw [h.pins.1.1] at this
    omega
  obtain ⟨_, χ, hχ, -⟩ := GlobalTheory.LamF.exists_kronecker_logOm_re D.host.E h.pins.1.1 hd4
  have g0 := (D.host.g_prime 0).pos
  have g1 := (D.host.g_prime 1).pos
  have hdpos : 0 < D.host.d := lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ((D.host.g 0 * D.host.g 1 * (Ideal.absNorm D.host.ccK * D.host.d) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hM : (0 : ℝ) < M := by
    rw [hMdef]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos g0 g1) (Nat.mul_pos hN hdpos)
  refine ⟨(C0 * ((fdeg D.host.E : ℝ) * D.R.r + |Real.log (M * (2 * xiR D))| + Real.log (dE D.host.E) +
    |(GlobalTheory.CM.logOm D.host.E χ).re|) ^ (2 : ℝ) * (1 + Real.log w.size) * w.size) *
      (Module.finrank ℚ T.Q.c.F : ℝ), fun F hFC hF hF1 => ?_⟩
  have hhol : rdU (T.U j T.σ₀) F ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) :=
    ((mem_cusp _ _ _ _ _ F).1 hFC).2 T.σ₀ T.good_σ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) hhol
  have hfin : supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) ≠ ⊤ :=
    supE_cusp_ne_top T.good_σ₀ hFC
  have hpos : 0 < supN (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
      (rdU (T.U j T.σ₀) F)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (h.supDef j hj (wtA w) w.n (dom_wtA w) T.σ₀ T.good_σ₀ F hFC heq.symm) hF1
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
    (rdU (T.U j T.σ₀) F) hpos hfin
  have hhalf : ∀ x ∈ ((T.U j T.σ₀).X k).dom, ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k)
      (rdU (T.U j T.σ₀) F k) x ≤
      2 * ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0 := by
    linarith
  obtain ⟨Xx, hX, hXg, hΛ, hk0⟩ := exists_dataX D T h j hj T.σ₀ T.good_σ₀ k
  have habs : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← GlobalTheory.TransvModel.xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]
  have htr : ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ,
        (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((M : ℂ) * τ.1 b) := by
    rw [← hX]
    intro v hv hiso b hb hbi
    have := GlobalTheory.TransvModel.transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (GlobalTheory.TransvModel.isIntegral_level_mul_kappa Xx.toData hN hdpos D.host.φ₀ (habs _)) v hv hiso b hb hbi
    rwa [hXg.trans h.pins.2.1.1, ← hMdef] at this
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((T.U j T.σ₀).X k) hX _ _ z0 M w.size (hSS k) hM
    (hwf k) w.one_le_size hr (fun v hv hvv b hb hbi => by
      obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
      exact ⟨γ, hγ, h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA w) k γ hγ, hγ'⟩) hz0 hhalf hposz
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * (2 * xiR D))| + 3 + Real.log (dE D.host.E) := by
    rw [hk0]
    have := le_abs_self (Real.log (M * (2 * xiR D)))
    have := abs_nonneg (Real.log (M * (2 * xiR D)))
    have := Real.log_nonneg hd1
    linarith
  obtain ⟨hLa1, hr'⟩ := hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) _ (GlobalTheory.CM.logOm D.host.E χ).re M Xx.k0 w.size
    hf1 hr Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos w.one_le_size hlog
  have hr'' := hr' _ _ (Nat.cast_nonneg _) (by positivity) hsz C0 2 le_rfl le_rfl
  have hNs : ∀ σ, IsNormOn (T.C j w) σ (T.Ns j w σ) := fun σ =>
    (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf
  have hSpos : ∀ σ, 0 < supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n F := fun σ =>
    lt_of_le_of_ne ((hNs σ).nonneg F hFC) fun h0 => hF1 ((hNs σ).defin F hFC h0.symm)
  have h5 := GlobalTheory.LamT.meanLogSup_lowerBound D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D)
    (h.unf j hj) (h.xiAbs j hj) (by rw [hpq]; exact hr) χ hχ (wtA w) w.n (dom_wtA w) F hFC hF hSpos k ⟨x, hx⟩ Xx hX
    D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  have hf' : Module.finrank ℚ D.host.E / 2 = D.R.f := hf
  rw [hf'] at h5
  have hK : (0 : ℝ) < Module.finrank ℚ T.Q.c.F := by exact_mod_cast Module.finrank_pos
  rw [← neg_mul, ← le_div_iff₀ hK]
  refine le_trans ?_ h5
  linarith

/- English proof (translation)
Set `Nf : TB.NormFam K C` to `{ N := fun σ F => N σ F nonneg := fun σ F => (hN σ).nonneg _ F.2 eq_zero := fun σ F h0 => Subtype.ext ((hN σ).defin _ F.2 h0) smul := fun σ a F => (hN σ).smul a _ F.2 add := fun σ F G => (hN σ).add _ F.2 _ G.2 }`. Conclude with `formalGroup_of_discriminant _ _ Nf _ (discriminant_of_product_lower _ _ Nf _ B fun F hF h0 => hB F.1 F.2 hF fun h1 => h0 (Subtype.ext h1))`.
-/
theorem fg_latOf_of_lowerBound {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] (C : Submodule K R) [FiniteDimensional K C]
    (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (N : (K →+* ℂ) → R → ℝ) (hN : ∀ σ, IsNormOn C σ (N σ)) (B : ℝ)
    (hB : ∀ F ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v F) → F ≠ 0 → -B ≤ ∑ σ : K →+* ℂ, Real.log (N σ F)) :
    (latOf C Vs hV).FG := by
  let Nf : TB.NormFam K C :=
    { N := fun σ F => N σ F
      nonneg := fun σ F => (hN σ).nonneg _ F.2
      eq_zero := fun σ F h0 => Subtype.ext ((hN σ).defin _ F.2 h0)
      smul := fun σ a F => (hN σ).smul a _ F.2
      add := fun σ F G => (hN σ).add _ F.2 _ G.2 }
  exact formalGroup_of_discriminant _ _ Nf _ (discriminant_of_product_lower _ _ Nf _ B fun F hF h0 =>
    hB F.1 F.2 hF fun h1 => h0 (Subtype.ext h1))

end GlobalTheory.IntCuspLat
