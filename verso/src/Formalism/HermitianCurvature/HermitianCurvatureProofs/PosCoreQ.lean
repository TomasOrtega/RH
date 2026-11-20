import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6 Formalism.FourierDecayAlt.P.JCTx6.Pos

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hIntG` using `Formalism.FourierDecayAlt.P.JCTx6.Int.intG`. Establish `hTrans` using `Formalism.FourierDecayAlt.P.JCTx6.Int.orbit_slice_integrable`. Take `⟨CcU, hCcU⟩` from `Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis 127 0`. Use `⟨max CcU 0, le_max_right _ _, ?_⟩` and prove the remaining obligations. Introduce `k ph n ρ Wp Wq _ _ _ _ _ _ z z' hz hz' Θ o κ hΘ χ A₀ ε hχ hε σ d t hd ht As mm A ho hκ hmm hAs hA hA₀`.

Establish `hw : (G.wMat (n + 1)).det ≠ 0` using `Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (n + 1)`. Use `set c₀ : ℂ := (U.hMat σ d).det * (t ^ (n + 1) * (G.wMat (n + 1)).det) with hc₀def`. Establish `hc₀ : c₀ ≠ 0` using `mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)`. Establish `hc₀n : 0 < ‖c₀‖` using `norm_pos_iff.mpr hc₀`. Take `⟨χD, hχD, hχD1, hχDs⟩` from `bump_exists hc₀`.

Take `⟨δ, hδ, hχε⟩` from `isCutG_scale hχ hε`. Use `set ε' : ℝ := δ * ε / (2 * ‖c₀‖) ^ 2 with hε'def`. Establish `hε' : 0 < ε'` using `by positivity`. Set `UD : U.UData k ph (n + 1) ρ Wp Wq Unit` to `⟨σ, d, z, z', fun _ => Θ, χD, fun x => χ (ε⁻¹ * x), δ * ε, ε', o, κ, 0, mm, As⟩`. Establish `hAs1 : 1 ≤ As` using `le_trans (Nat.one_le_pow _ _ (by omega)) hAs`.

Establish `hOk : UD.Ok 0`. Use `⟨hd, by omega, hz, hz', fun _ => hΘ, hχD, hχε, hε', ?_, ho, hκ, by simp [UD], hmm, hAs, by simpa using hAs1⟩` and prove the remaining obligations. Introduce `w hw'`. Establish `h2` using `(hχDs w hw').2`. Establish `h3 : ‖w‖ ^ 2 ≤ (2 * ‖c₀‖) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) h2 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `hA₀U : CcU * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀`. Use `le_trans ?_ hA₀` and prove the remaining obligations. Use `gcongr`. Conclude with `le_max_left _ _`.

Take `⟨ha1, -, -, C, hC⟩` from `hCcU k ph (n + 1) ρ Wp Wq Unit UD hOk A₀ hA₀U`. Use `set a := UD.a 0 A₀ with ha_def`. Use `set Iv : ℝ := ∫ v, (1 + ‖v‖) ^ (-a) ∂(G.muPi U.betaU (G.UT (n + 1))) with hIv`. Use `⟨ε', max (Real.pi ^ ((n + 1) * n / 2) * (C * (min 1 ‖t‖) ^ (-a) * Iv)) 0, hε', le_max_right _ _, ?_⟩` and prove the remaining obligations. Introduce `f c hc F hF`.

Establish `hc0 : 0 ≤ c` using `Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc`. Take `⟨V, indexVFirst, indexVSecond, hVc, ⟨MM⟩⟩` from `Formalism.FourierDecayAlt.P.compactly_supported_banach_model k ρ (Unit → (Wq →L[ℂ] Wp)) (UD.a 0 A₀) mm UD.S`. Take `⟨Φ, hΦev, hΦreg⟩` from `hC f c hc V MM`. Take `⟨C1, hC1⟩` from `Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k (ph + (n + 1)) ρ Wp Wq z z' o κ Θ χD (fun x => χ (ε⁻¹ * x)) (δ * ε) hΘ hχD hχε 0 (3 * As) A₀ (by omega)`. Establish `hStar` using `hC1 f c hc`.

Use `set F₁ := B.opApply Θ (U.cutDG k (ph + (n + 1)) ρ z z' χD (fun x => χ (ε⁻¹ * x)) f) with hF₁def`. Establish `hB : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g = c₀ → F g = F₁ g`. Introduce `g hg hgc`. Rewrite using `[hF g hg (by rw [hgc]; exact hc₀)]`. Use `opApply_congr_open Θ (O := {x | dist (U.DjU k (ph + (n + 1)) ρ x) c₀ < ‖c₀‖ / 4}) ?_ ?_ g ?_` and prove the remaining obligations.

Conclude with `isOpen_lt ((cont_DjU k (ph + (n + 1)) ρ).dist continuous_const) continuous_const`. Introduce `x hx`. Simplify using `only [U.cutDG]`. Rewrite using `[hχD1 _ (le_of_lt hx), one_mul, div_eq_inv_mul]`. Use `show dist _ c₀ < ‖c₀‖ / 4`.

Rewrite using `[hgc, dist_self]`. Check the signs of the components of the expression. Establish `hZne : ∀ v : G.UT (n + 1) → ℂ, G.detM (Zv n t v) ≠ 0`. Introduce `v`. Establish `e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det` using `detM_Zv n t v`.

Rewrite using `[e]`. Conclude with `mul_ne_zero (pow_ne_zero _ ht) hw`. Establish `hOrb : ∀ (ξ : U.Xi k ph (n + 1) ρ σ) (v : G.UT (n + 1) → ℂ) (γ : B.Mat k ρ), γ ∈ B.GV k ρ → F (U.gaXi k ρ σ d ξ (Zv n t v) γ) = F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ)`. Introduce `ξ v γ hγ`. Apply `hB _ (Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ _ (hZne v) hγ)` to reduce the goal to its premises.

Rewrite using `[Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice]`. Establish `e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det` using `detM_Zv n t v`. Rewrite using `[e]`. Establish `hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD)` using `hχD.2.1.isCompact.image continuous_norm`. Establish `hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0`.

Introduce and unpack `_ ⟨w, hw', rfl⟩`. Conclude with `lt_of_lt_of_le (by positivity) (hχDs w hw').1`. Establish `hthr : 2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) < (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) - 2 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) * ((0 + o : ℕ) : ℝ)) / (8 * (2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1))`. Establish `hnd : ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) ≤ (As : ℝ)`. Establish `h1 : 2 * (ph + (n + 1) + ρ) + k + 1 ≤ (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3` using `Nat.le_self_pow (by norm_num) _`.

Conclude with `h1.trans hAs` after adjusting the coercions. Establish `ha1'` using `ha1`. Simplify using `only [ha_def, U.UData.a, U.a1] at ha1'`. Use `set R : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) with hR`. Establish `hR0 : 0 ≤ R` using `Nat.cast_nonneg _`.

Establish `hD : 0 < 8 * (2 * R + 1)` using `by positivity`. Use `set Nd : ℝ := ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) with hNd`. Establish `hNd1 : 1 ≤ Nd` using `by rw [hNd]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)`. Establish `hle : (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) - 2 * (R + 1) * (((0 * (n + 1) ^ 2 + 1 + mm) + o : ℕ) : ℝ) - 5 * R * (((0 * (n + 1) ^ 2 : ℕ) : ℝ) + 1) - 2 * R * (mm : ℝ)) / (8 * (2 * R + 1)) ≤ (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) - 2 * (R + 1) * ((0 + o : ℕ …`. Apply `div_le_div_of_nonneg_right _ hD.le` to reduce the goal to its premises.

Use `push_cast`. Establish `hm0 : (0 : ℝ) ≤ mm` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlt : 2 * R * Nd < (((127 : ℕ) : ℝ) + 1) * (R + 1) ^ 3 * (As : ℝ)`. Establish `hAs' : (1 : ℝ) ≤ As` using `by exact_mod_cast hAs1`.

Establish `h1 : 2 * R * Nd < 128 * (R + 1) * Nd` using `by nlinarith`. Establish `h2 : 128 * (R + 1) * Nd ≤ 128 * (R + 1) ^ 3 * (As : ℝ)`. Establish `h3 : (R + 1) ≤ (R + 1) ^ 3` using `le_self_pow₀ (by linarith) (by norm_num)`. Establish `h4 : (R + 1) * Nd ≤ (R + 1) ^ 3 * (As : ℝ)` using `mul_le_mul h3 hnd (by linarith) (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.

Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `lt_of_lt_of_le hlt (le_trans ha1' hle)`. Establish `hInt : ∀ γ ∈ B.GV k ρ, Integrable (gInt k ph n ρ σ d t z z' F γ) (muG k ph n ρ σ)`. Introduce `γ hγ`.

Establish `h1` using `hIntG k ph n ρ σ d t hd ht _ hK hK0 0 _ hthr z z' (Wq →L[ℂ] Wp) F₁ (C1 * c) hStar γ hγ`. Establish `e : gInt k ph n ρ σ d t z z' F γ = gInt k ph n ρ σ d t z z' F₁ γ`. Use function extensionality and compare the values at `y`. Unfold `gInt`. Establish `e1 : U.gaXi k ρ σ d (y.1, y.2.1) (Matrix.of.symm (t • G.wMat (n + 1) * G.upper y.2.2)) γ = U.gaXi k ρ σ d (y.1, y.2.1) (Zv n t y.2.2) γ` using `rfl`.

Rewrite using `[e1, hOrb _ _ γ hγ]`. Rewrite using `[e]`. Conclude with `h1`. Establish `hcore : ∀ γ ∈ B.GV k ρ, U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ = ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) • G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t := fun γ hγ => Dx2.SL.core σ d t z z' F γ (hTrans k ph n ρ σ d t z …`. Establish `ha128 : 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) ≤ a`.

Establish `h` using `ha1`. Evaluate the numerical expressions using `at h ⊢`. Conclude with `h`. Establish `ha0 : 0 ≤ a` using `le_trans (by positivity) ha128`. Establish `hZc : Continuous (fun v : G.UT (n + 1) → ℂ => Zv n t v)` using `by show Continuous (fun v : G.UT (n + 1) → ℂ => (G.ptLong (n + 1) t * G.upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))`.

Conclude with `continuous_const.matrix_mul Dx2.SL.cont_upper`. Establish `hΦc : Continuous (fun v : G.UT (n + 1) → ℂ => Φ (Zv n t v))` using `continuous_iff_continuousAt.2 fun v => ((hΦreg _ (hZne v)).1.continuousAt).comp hZc.continuousAt`. Establish `hψc : Continuous (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v)))`. Establish `h1 : Continuous fun v : G.UT (n + 1) → ℂ => G.superSum (G.upper v)`. Unfold `G.superSum`.

Conclude with `continuous_finsetSum _ fun i _ => (continuous_apply _).comp ((continuous_apply _).comp Dx2.SL.cont_upper)`. Unfold `G.psi`. Conclude with `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul h1))))`. Establish `hCc : 0 ≤ C * c`. Establish `h` using `(hΦreg _ (hZne 0)).2 0 (Nat.zero_le _)`.

Rewrite `h` using `[norm_iteratedFDeriv_zero]`. Establish `hp : 0 < (1 + ‖Zv n t 0‖) ^ (-a)` using `Real.rpow_pos_of_pos (by positivity) _`. Assume the negation of the conclusion as `hneg`. Use `mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hp` as an intermediate fact. Combine the linear relations using `[norm_nonneg (Φ (Zv n t 0))]`.

Establish `hbound : ∀ v : G.UT (n + 1) → ℂ, ‖G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v)‖ ≤ C * c * (min 1 ‖t‖) ^ (-a) * (1 + ‖v‖) ^ (-a)`. Introduce `v`. Rewrite using `[norm_smul, Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_psi, one_mul]`. Establish `h` using `(hΦreg _ (hZne v)).2 0 (Nat.zero_le _)`. Rewrite `h` using `[norm_iteratedFDeriv_zero]`.

Use `h.trans ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (Zv_decay n ht v ha0) hCc` as an intermediate fact. Rewrite `this` using `[← mul_assoc]`. Conclude with `this`. Establish `hfin : (Module.finrank ℝ (G.UT (n + 1) → ℂ) : ℝ) < a`.

Establish `e : Module.finrank ℝ (G.UT (n + 1) → ℂ) = Fintype.card (G.UT (n + 1)) * 2`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex]`. Establish `hcard : Fintype.card (G.UT (n + 1)) ≤ (n + 1) * (n + 1)`. Use `Fintype.card_subtype_le (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)` as an intermediate fact.

Simplify `this` using `[Fintype.card_prod, Fintype.card_fin]`. Establish `hcardR : ((Fintype.card (G.UT (n + 1)) * 2 : ℕ) : ℝ) ≤ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1))`. Establish `: Fintype.card (G.UT (n + 1)) * 2 ≤ 2 * ((n + 1) * (n + 1))` using `by omega`. Conclude with `this` after adjusting the coercions. Rewrite using `[e]`.

Use `lt_of_le_of_lt hcardR (lt_of_lt_of_le ?_ ha128)` and prove the remaining obligations. Establish `hn : ((n : ℝ) + 1) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1` using `by push_cast; linarith [(Nat.cast_nonneg ph : (0:ℝ) ≤ ph), (Nat.cast_nonneg ρ : (0:ℝ) ≤ ρ)]`. Establish `hAs' : (1 : ℝ) ≤ As` using `by exact_mod_cast hAs1`. Use `set R1 : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1`. Establish `hR1 : 1 ≤ R1`.

Establish `: (0 : ℝ) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : (1 : ℝ) ≤ (n : ℝ) + 1` using `by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]`. Establish `h1 : 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ 2 * (R1 * R1)` using `by gcongr`. Establish `h2 : 2 * (R1 * R1) < 128 * R1 ^ 3` using `by nlinarith`.

Establish `h3 : 128 * R1 ^ 3 ≤ 128 * R1 ^ 3 * (As : ℝ)` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hφint : Integrable (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v)) (G.muPi U.betaU (G.UT (n + 1)))`. Rewrite using `[Dx2.SL.muPi_betaU]`. Apply `Integrable.smul_measure_nnreal` to reduce the goal to its premises.

Conclude with `((integrable_one_add_norm hfin).const_mul (C * c * (min 1 ‖t‖) ^ (-a))).mono' (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)`. Use `set W₀ : V := ∫ v, G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v) ∂(G.muPi U.betaU (G.UT (n + 1))) with hW₀`. Use `set Wf : V := ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) • W₀ with hWf`. Establish `key : ∀ γ ∈ B.GV k ρ, U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ = MM.ev Wf γ () := by`. Introduce `γ hγ`.

Establish `hgN : 0 < B.gN γ ^ a` using `Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.Ux1.gN_pos hγ) a`. Set `L₀ : V →ₗ[ℂ] (Wq →L[ℂ] Wp)` to `(LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Wq →L[ℂ] Wp) ()) ∘ₗ (LinearMap.proj (R := ℂ) (φ := fun _ : B.Mat k ρ => Unit → (Wq →L[ℂ] Wp)) γ) ∘ₗ MM.ev`. Establish `hL₀ : ∀ w, L₀ w = MM.ev w γ ()` using `fun w => rfl`. Establish `hbd : ∀ w, ‖L₀ w‖ ≤ (B.gN γ ^ a)⁻¹ * ‖w‖`. Introduce `w`.

Rewrite using `[hL₀]`. Establish `h1` using `(MM.mem w).2 [] [] (by simp) (by simp) (by simp) γ hγ`. Rewrite using `[inv_mul_eq_div, le_div_iff₀' hgN]`. Conclude with `le_trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ ()) hgN.le) h1`. Set `L : V →L[ℂ] (Wq →L[ℂ] Wp)` to `L₀.mkContinuous _ hbd`.

Establish `hL : ∀ w, L w = MM.ev w γ ()` using `fun w => rfl`. Establish `hΨ : ∀ v : G.UT (n + 1) → ℂ, U.PhiFun (p` using `ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ = MM.ev (Φ (Zv n t v)) γ () := by`. Introduce `v`. Rewrite using `[hΦev _ (hZne v) γ hγ]`. Use `show _ = (U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' (UD.F1 f) (Zv n t v) γ) ()`.

Unfold `U.PhiFun`. Establish `e` using `(ContinuousLinearEquiv.funUnique Unit ℂ (Wq →L[ℂ] Wp)).integral_comp_comm (μ := U.muXi k ph (n + 1) ρ σ) (fun ξ => U.psiStar k ρ σ z z' ξ • UD.F1 f (U.gaXi k ρ σ d ξ (Zv n t v) γ))`. Use `Eq.trans ?_ e` and prove the remaining obligations. Use `integral_congr_ae (Eventually.of_forall fun ξ => ?_)` and prove the remaining obligations. Use `show U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (Zv n t v) γ) = U.psiStar k ρ σ z z' ξ • F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ)`.

Rewrite using `[hOrb ξ v γ hγ]`. Rewrite using `[hcore γ hγ]`. Establish `hOm : G.OmLong U.betaU n (fun Z => U.PhiFun (p` using `ph) (s := n + 1) k ρ σ d z z' F Z γ) t = L W₀ := by`. Rewrite using `[hW₀, ← L.integral_comp_comm hφint]`. Unfold `G.OmLong`.

Use `integral_congr_ae (Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Use `show G.psi U.betaU (G.superSum (G.upper v)) • U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ = L (G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))`. Rewrite using `[L.map_smul, hL, hΨ v]`. Rewrite using `[hOm, hL, hWf, map_smul]`. Both sides reduce to the same expression.

Establish `hAa : A ≤ a` using `le_trans hA ha128`. Establish `hCC : B.CCle A mm (fun γ => MM.ev Wf γ ()) ‖Wf‖` using `Formalism.FourierDecayAlt.P.compactly_supported_monotone k ρ (Wq →L[ℂ] Wp) a A ‖Wf‖ mm _ hAa (ccle_unit (MM.mem Wf))`. Establish `hCC' : B.CCle A mm (fun γ => U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) ‖Wf‖ := Formalism.FourierDecayAlt.P.Ux1.cc_congr (fun γ hγ => (key γ hγ).symm) hCC`. Establish `hgint : Integrable (fun v : G.UT (n + 1) → ℂ => C * c * (min 1 ‖t‖) ^ (-a) * (1 + ‖v‖) ^ (-a)) (G.muPi U.betaU (G.UT (n + 1)))`. Rewrite using `[Dx2.SL.muPi_betaU]`.

Apply `Integrable.smul_measure_nnreal` to reduce the goal to its premises. Conclude with `(integrable_one_add_norm hfin).const_mul _`. Establish `hW0 : ‖W₀‖ ≤ C * c * (min 1 ‖t‖) ^ (-a) * Iv`. Rewrite using `[hW₀]`. Use `(norm_integral_le_of_norm_le hgint (Eventually.of_forall hbound)).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[hIv, ← MeasureTheory.integral_const_mul]`. Establish `hWfb : ‖Wf‖ ≤ max (Real.pi ^ ((n + 1) * n / 2) * (C * (min 1 ‖t‖) ^ (-a) * Iv)) 0 * c`. Rewrite using `[hWf, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hCC' hWfb, ?_, fun γ hγ => hTrans k ph n ρ σ d t z z' _ F γ (hInt γ hγ)⟩` and prove the remaining obligations.

Introduce `γ hγ hne`. Assume the negation of the conclusion as `hlt`. Establish `hnot : γ ∉ UD.S` using `fun h => hlt h`. Apply `hne` to reduce the goal to its premises. Rewrite using `[key γ hγ, MM.off Wf γ hγ hnot]`.

Both sides reduce to the same expression.
-/
theorem posCoreQ : ∃ Cc : ℝ, 0 ≤ Cc ∧
  ∀ (k ph n ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ), inWb k (ph + (n + 1) + ρ) z → inWb k (ph + (n + 1) + ρ) z' →
    ∀ (Θ : B.DiffOp k (ph + (n + 1) + ρ) Wp Wq) (o κ : ℕ), U.InDD k (ph + (n + 1)) ρ o κ Θ →
    ∀ (χ : ℝ → ℝ) (A₀ ε : ℝ), C6.IsCut0 χ → 0 < ε →
    ∀ (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ), (∀ i, d i ≠ 0) → t ≠ 0 →
    ∀ (As mm : ℕ) (A : ℝ), o ≤ As → κ + (ph + (n + 1)) * o ≤ As → mm ≤ As →
      (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 ≤ As →
      A ≤ 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) →
      Cc * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ →
      ∃ ε' K : ℝ, 0 < ε' ∧ 0 ≤ K ∧
      ∀ (f : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * As) f c →
      ∀ F : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp),
        (∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
          F g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) z z' x / ε) : ℝ) : ℂ) • f x) g) →
        B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
          (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) (K * c) ∧
        (∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
          (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ ≠ 0 →
          ε' ≤ Gf k ρ (U.lowV k (ph + (n + 1)) ρ z) (U.lowV k (ph + (n + 1)) ρ z') γ) ∧
        ∀ γ ∈ B.GV k ρ, Integrable (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (Dx2.SL.sigP σ) =>
          U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) z z' ξ •
            F (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) ξ (fun a => a.elim0) γ))
          (U.muXi k (ph + (n + 1)) 0 ρ (Dx2.SL.sigP σ)) := by
  have hIntG := Formalism.FourierDecayAlt.P.JCTx6.Int.intG
  have hTrans := Formalism.FourierDecayAlt.P.JCTx6.Int.orbit_slice_integrable
  obtain ⟨CcU, hCcU⟩ := Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis 127 0
  refine ⟨max CcU 0, le_max_right _ _, ?_⟩
  intro k ph n ρ Wp Wq _ _ _ _ _ _ z z' hz hz' Θ o κ hΘ χ A₀ ε hχ hε σ d t hd ht As mm A ho hκ
    hmm hAs hA hA₀

  have hw : (G.wMat (n + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (n + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t ^ (n + 1) * (G.wMat (n + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)
  have hc₀n : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := bump_exists hc₀
  obtain ⟨δ, hδ, hχε⟩ := isCutG_scale hχ hε
  set ε' : ℝ := δ * ε / (2 * ‖c₀‖) ^ 2 with hε'def
  have hε' : 0 < ε' := by positivity
  let UD : U.UData k ph (n + 1) ρ Wp Wq Unit :=
    ⟨σ, d, z, z', fun _ => Θ, χD, fun x => χ (ε⁻¹ * x), δ * ε, ε', o, κ, 0, mm, As⟩
  have hAs1 : 1 ≤ As := le_trans (Nat.one_le_pow _ _ (by omega)) hAs
  have hOk : UD.Ok 0 := by
    refine ⟨hd, by omega, hz, hz', fun _ => hΘ, hχD, hχε, hε', ?_, ho, hκ, by simp [UD], hmm, hAs,
      by simpa using hAs1⟩
    intro w hw'
    have h2 := (hχDs w hw').2
    have h3 : ‖w‖ ^ 2 ≤ (2 * ‖c₀‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc ε' * ‖w‖ ^ 2 ≤ ε' * (2 * ‖c₀‖) ^ 2 := mul_le_mul_of_nonneg_left h3 hε'.le
      _ = δ * ε := by rw [hε'def]; field_simp
  have hA₀U : CcU * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ := by
    refine le_trans ?_ hA₀
    gcongr
    exact le_max_left _ _
  obtain ⟨ha1, -, -, C, hC⟩ := hCcU k ph (n + 1) ρ Wp Wq Unit UD hOk A₀ hA₀U
  set a := UD.a 0 A₀ with ha_def
  set Iv : ℝ := ∫ v, (1 + ‖v‖) ^ (-a) ∂(G.muPi U.betaU (G.UT (n + 1))) with hIv
  refine ⟨ε', max (Real.pi ^ ((n + 1) * n / 2) * (C * (min 1 ‖t‖) ^ (-a) * Iv)) 0, hε', le_max_right _ _, ?_⟩
  intro f c hc F hF
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  obtain ⟨V, indexVFirst, indexVSecond, hVc, ⟨MM⟩⟩ :=
    Formalism.FourierDecayAlt.P.compactly_supported_banach_model k ρ (Unit → (Wq →L[ℂ] Wp)) (UD.a 0 A₀) mm UD.S
  obtain ⟨Φ, hΦev, hΦreg⟩ := hC f c hc V MM

  obtain ⟨C1, hC1⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k (ph + (n + 1)) ρ Wp Wq z z' o κ Θ χD
    (fun x => χ (ε⁻¹ * x)) (δ * ε) hΘ hχD hχε 0 (3 * As) A₀ (by omega)
  have hStar := hC1 f c hc
  set F₁ := B.opApply Θ (U.cutDG k (ph + (n + 1)) ρ z z' χD (fun x => χ (ε⁻¹ * x)) f) with hF₁def

  have hB : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g = c₀ → F g = F₁ g := by
    intro g hg hgc
    rw [hF g hg (by rw [hgc]; exact hc₀)]
    refine opApply_congr_open Θ (O := {x | dist (U.DjU k (ph + (n + 1)) ρ x) c₀ < ‖c₀‖ / 4}) ?_ ?_ g ?_
    · exact isOpen_lt ((cont_DjU k (ph + (n + 1)) ρ).dist continuous_const) continuous_const
    · intro x hx
      simp only [U.cutDG]
      rw [hχD1 _ (le_of_lt hx), one_mul, div_eq_inv_mul]
    · show dist _ c₀ < ‖c₀‖ / 4
      rw [hgc, dist_self]; positivity
  have hZne : ∀ v : G.UT (n + 1) → ℂ, G.detM (Zv n t v) ≠ 0 := by
    intro v
    have e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det := detM_Zv n t v
    rw [e]; exact mul_ne_zero (pow_ne_zero _ ht) hw
  have hOrb : ∀ (ξ : U.Xi k ph (n + 1) ρ σ) (v : G.UT (n + 1) → ℂ) (γ : B.Mat k ρ), γ ∈ B.GV k ρ →
      F (U.gaXi k ρ σ d ξ (Zv n t v) γ) = F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ) := by
    intro ξ v γ hγ
    apply hB _ (Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ _
      (hZne v) hγ)
    rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice]
    have e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det := detM_Zv n t v
    rw [e]

  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) -
        2 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) * ((0 + o : ℕ) : ℝ)) /
        (8 * (2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1)) := by
    have hnd : ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) ≤ (As : ℝ) := by
      have h1 : 2 * (ph + (n + 1) + ρ) + k + 1 ≤ (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 :=
        Nat.le_self_pow (by norm_num) _
      exact_mod_cast h1.trans hAs
    have ha1' := ha1
    simp only [ha_def, U.UData.a, U.a1] at ha1'
    set R : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) with hR
    have hR0 : 0 ≤ R := Nat.cast_nonneg _
    have hD : 0 < 8 * (2 * R + 1) := by positivity
    set Nd : ℝ := ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) with hNd
    have hNd1 : 1 ≤ Nd := by rw [hNd]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hle : (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) -
          2 * (R + 1) * (((0 * (n + 1) ^ 2 + 1 + mm) + o : ℕ) : ℝ) - 5 * R * (((0 * (n + 1) ^ 2 : ℕ) : ℝ) + 1) -
          2 * R * (mm : ℝ)) / (8 * (2 * R + 1)) ≤
        (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) - 2 * (R + 1) * ((0 + o : ℕ) : ℝ)) /
          (8 * (2 * R + 1)) := by
      apply div_le_div_of_nonneg_right _ hD.le
      push_cast
      have hm0 : (0 : ℝ) ≤ mm := Nat.cast_nonneg _
      nlinarith
    have hlt : 2 * R * Nd < (((127 : ℕ) : ℝ) + 1) * (R + 1) ^ 3 * (As : ℝ) := by
      have hAs' : (1 : ℝ) ≤ As := by exact_mod_cast hAs1
      have h1 : 2 * R * Nd < 128 * (R + 1) * Nd := by nlinarith
      have h2 : 128 * (R + 1) * Nd ≤ 128 * (R + 1) ^ 3 * (As : ℝ) := by
        have h3 : (R + 1) ≤ (R + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
        have h4 : (R + 1) * Nd ≤ (R + 1) ^ 3 * (As : ℝ) :=
          mul_le_mul h3 hnd (by linarith) (by positivity)
        nlinarith
      norm_num
      linarith
    exact lt_of_lt_of_le hlt (le_trans ha1' hle)

  have hInt : ∀ γ ∈ B.GV k ρ, Integrable (gInt k ph n ρ σ d t z z' F γ) (muG k ph n ρ σ) := by
    intro γ hγ
    have h1 := hIntG k ph n ρ σ d t hd ht _ hK hK0 0 _ hthr z z' (Wq →L[ℂ] Wp) F₁ (C1 * c) hStar γ hγ
    have e : gInt k ph n ρ σ d t z z' F γ = gInt k ph n ρ σ d t z z' F₁ γ := by
      funext y
      unfold gInt
      have e1 : U.gaXi k ρ σ d (y.1, y.2.1) (Matrix.of.symm (t • G.wMat (n + 1) * G.upper y.2.2)) γ =
          U.gaXi k ρ σ d (y.1, y.2.1) (Zv n t y.2.2) γ := rfl
      rw [e1, hOrb _ _ γ hγ]
    rw [e]; exact h1
  have hcore : ∀ γ ∈ B.GV k ρ,
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ =
        ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) •
          G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t :=
    fun γ hγ => Dx2.SL.core σ d t z z' F γ (hTrans k ph n ρ σ d t z z' _ F γ (hInt γ hγ))

  have ha128 : 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) ≤ a := by
    have h := ha1
    norm_num at h ⊢
    exact h
  have ha0 : 0 ≤ a := le_trans (by positivity) ha128
  have hZc : Continuous (fun v : G.UT (n + 1) → ℂ => Zv n t v) := by
    show Continuous (fun v : G.UT (n + 1) → ℂ =>
      (G.ptLong (n + 1) t * G.upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    exact continuous_const.matrix_mul Dx2.SL.cont_upper
  have hΦc : Continuous (fun v : G.UT (n + 1) → ℂ => Φ (Zv n t v)) :=
    continuous_iff_continuousAt.2 fun v => ((hΦreg _ (hZne v)).1.continuousAt).comp hZc.continuousAt
  have hψc : Continuous (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v))) := by
    have h1 : Continuous fun v : G.UT (n + 1) → ℂ => G.superSum (G.upper v) := by
      unfold G.superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp Dx2.SL.cont_upper)
    unfold G.psi
    exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul h1))))
  have hCc : 0 ≤ C * c := by
    have h := (hΦreg _ (hZne 0)).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    have hp : 0 < (1 + ‖Zv n t 0‖) ^ (-a) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hp
    linarith [norm_nonneg (Φ (Zv n t 0))]
  have hbound : ∀ v : G.UT (n + 1) → ℂ, ‖G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v)‖ ≤
      C * c * (min 1 ‖t‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro v
    rw [norm_smul, Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_psi, one_mul]
    have h := (hΦreg _ (hZne v)).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_left (Zv_decay n ht v ha0) hCc
    rw [← mul_assoc] at this
    exact this
  have hfin : (Module.finrank ℝ (G.UT (n + 1) → ℂ) : ℝ) < a := by
    have e : Module.finrank ℝ (G.UT (n + 1) → ℂ) = Fintype.card (G.UT (n + 1)) * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    have hcard : Fintype.card (G.UT (n + 1)) ≤ (n + 1) * (n + 1) := by
      have := Fintype.card_subtype_le (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    have hcardR : ((Fintype.card (G.UT (n + 1)) * 2 : ℕ) : ℝ) ≤ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
      have : Fintype.card (G.UT (n + 1)) * 2 ≤ 2 * ((n + 1) * (n + 1)) := by omega
      exact_mod_cast this
    rw [e]
    refine lt_of_le_of_lt hcardR (lt_of_lt_of_le ?_ ha128)
    have hn : ((n : ℝ) + 1) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg ph : (0:ℝ) ≤ ph), (Nat.cast_nonneg ρ : (0:ℝ) ≤ ρ)]
    have hAs' : (1 : ℝ) ≤ As := by exact_mod_cast hAs1
    set R1 : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1
    have hR1 : 1 ≤ R1 := by
      have : (0 : ℝ) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hn0 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h1 : 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ 2 * (R1 * R1) := by gcongr
    have h2 : 2 * (R1 * R1) < 128 * R1 ^ 3 := by nlinarith
    have h3 : 128 * R1 ^ 3 ≤ 128 * R1 ^ 3 * (As : ℝ) := by nlinarith
    linarith
  have hφint : Integrable (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))
      (G.muPi U.betaU (G.UT (n + 1))) := by
    rw [Dx2.SL.muPi_betaU]
    apply Integrable.smul_measure_nnreal
    exact ((integrable_one_add_norm hfin).const_mul (C * c * (min 1 ‖t‖) ^ (-a))).mono'
      (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)

  set W₀ : V := ∫ v, G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v) ∂(G.muPi U.betaU (G.UT (n + 1)))
    with hW₀
  set Wf : V := ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) • W₀ with hWf
  have key : ∀ γ ∈ B.GV k ρ,
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ =
        MM.ev Wf γ () := by
    intro γ hγ
    have hgN : 0 < B.gN γ ^ a := Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.Ux1.gN_pos hγ) a
    let L₀ : V →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Wq →L[ℂ] Wp) ()) ∘ₗ
        (LinearMap.proj (R := ℂ) (φ := fun _ : B.Mat k ρ => Unit → (Wq →L[ℂ] Wp)) γ) ∘ₗ MM.ev
    have hL₀ : ∀ w, L₀ w = MM.ev w γ () := fun w => rfl
    have hbd : ∀ w, ‖L₀ w‖ ≤ (B.gN γ ^ a)⁻¹ * ‖w‖ := by
      intro w
      rw [hL₀]
      have h1 := (MM.mem w).2 [] [] (by simp) (by simp) (by simp) γ hγ
      rw [inv_mul_eq_div, le_div_iff₀' hgN]
      exact le_trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ ()) hgN.le) h1
    let L : V →L[ℂ] (Wq →L[ℂ] Wp) := L₀.mkContinuous _ hbd
    have hL : ∀ w, L w = MM.ev w γ () := fun w => rfl
    have hΨ : ∀ v : G.UT (n + 1) → ℂ,
        U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ = MM.ev (Φ (Zv n t v)) γ () := by
      intro v
      rw [hΦev _ (hZne v) γ hγ]
      show _ = (U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' (UD.F1 f) (Zv n t v) γ) ()
      unfold U.PhiFun
      have e := (ContinuousLinearEquiv.funUnique Unit ℂ (Wq →L[ℂ] Wp)).integral_comp_comm
        (μ := U.muXi k ph (n + 1) ρ σ)
        (fun ξ => U.psiStar k ρ σ z z' ξ • UD.F1 f (U.gaXi k ρ σ d ξ (Zv n t v) γ))
      refine Eq.trans ?_ e
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      show U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (Zv n t v) γ) =
        U.psiStar k ρ σ z z' ξ • F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ)
      rw [hOrb ξ v γ hγ]
    rw [hcore γ hγ]
    have hOm : G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t = L W₀ := by
      rw [hW₀, ← L.integral_comp_comm hφint]
      unfold G.OmLong
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      show G.psi U.betaU (G.superSum (G.upper v)) • U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ =
        L (G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))
      rw [L.map_smul, hL, hΨ v]
    rw [hOm, hL, hWf, map_smul]
    rfl

  have hAa : A ≤ a := le_trans hA ha128
  have hCC : B.CCle A mm (fun γ => MM.ev Wf γ ()) ‖Wf‖ :=
    Formalism.FourierDecayAlt.P.compactly_supported_monotone k ρ (Wq →L[ℂ] Wp) a A ‖Wf‖ mm _ hAa (ccle_unit (MM.mem Wf))
  have hCC' : B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
      (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) ‖Wf‖ :=
    Formalism.FourierDecayAlt.P.Ux1.cc_congr (fun γ hγ => (key γ hγ).symm) hCC
  have hgint : Integrable (fun v : G.UT (n + 1) → ℂ => C * c * (min 1 ‖t‖) ^ (-a) * (1 + ‖v‖) ^ (-a))
      (G.muPi U.betaU (G.UT (n + 1))) := by
    rw [Dx2.SL.muPi_betaU]
    apply Integrable.smul_measure_nnreal
    exact (integrable_one_add_norm hfin).const_mul _
  have hW0 : ‖W₀‖ ≤ C * c * (min 1 ‖t‖) ^ (-a) * Iv := by
    rw [hW₀]
    refine (norm_integral_le_of_norm_le hgint (Eventually.of_forall hbound)).trans (le_of_eq ?_)
    rw [hIv, ← MeasureTheory.integral_const_mul]
  have hWfb : ‖Wf‖ ≤ max (Real.pi ^ ((n + 1) * n / 2) * (C * (min 1 ‖t‖) ^ (-a) * Iv)) 0 * c := by
    rw [hWf, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc Real.pi ^ ((n + 1) * n / 2) * ‖W₀‖ ≤ Real.pi ^ ((n + 1) * n / 2) * (C * c * (min 1 ‖t‖) ^ (-a) * Iv) :=
          mul_le_mul_of_nonneg_left hW0 (by positivity)
      _ = (Real.pi ^ ((n + 1) * n / 2) * (C * (min 1 ‖t‖) ^ (-a) * Iv)) * c := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hc0
  refine ⟨Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hCC' hWfb, ?_, fun γ hγ => hTrans k ph n ρ σ d t z z' _ F γ (hInt γ hγ)⟩
  intro γ hγ hne
  by_contra hlt
  have hnot : γ ∉ UD.S := fun h => hlt h
  apply hne
  rw [key γ hγ, MM.off Wf γ hγ hnot]
  rfl

end Formalism.FourierDecayAlt.P.PBE
