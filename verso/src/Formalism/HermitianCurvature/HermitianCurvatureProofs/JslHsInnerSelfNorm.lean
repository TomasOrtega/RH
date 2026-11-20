import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEPairAtDeriv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section JSL

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Establish `h0 : f x = 0` using `h.eq_of_nhds`. Establish `hd : fderiv ℝ f x = 0`. Rewrite using `[h.fderiv_eq]`. Conclude with `fderiv_const_apply (0 : E)`. Use `fin_cases j`.

Use `show pOp l f x = 0`. Unfold `pOp QuantumDeterminants.wirt`. Rewrite using `[hd]`. Simplify using the standard rewrite rules. Use `show cOp l f x = 0`.

Simplify using `[cOp, h0]`. Use `show ciOp l f x = 0`. Simplify using `[ciOp, h0]`. Use `show pbOp l f x = 0`. Unfold `pbOp QuantumDeterminants.wirtBar`.

Rewrite using `[hd]`. Simplify using the standard rewrite rules. Use `show cbOp l f x = 0`. Simplify using `[cbOp, h0]`. Use `show cbiOp l f x = 0`.

Simplify using `[cbiOp, h0]`.
-/
private theorem opL_eq_zero_of_eventuallyEq_zero {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m)
    (j : Fin 6) (f : (Fin m → ℂ) → E) (x : Fin m → ℂ) (h : f =ᶠ[𝓝 x] 0) : opL l j f x = 0 := by
  have h0 : f x = 0 := h.eq_of_nhds
  have hd : fderiv ℝ f x = 0 := by
    rw [h.fderiv_eq]
    exact fderiv_const_apply (0 : E)
  fin_cases j
  · show pOp l f x = 0
    unfold pOp QuantumDeterminants.wirt
    rw [hd]
    simp
  · show cOp l f x = 0
    simp [cOp, h0]
  · show ciOp l f x = 0
    simp [ciOp, h0]
  · show pbOp l f x = 0
    unfold pbOp QuantumDeterminants.wirtBar
    rw [hd]
    simp
  · show cbOp l f x = 0
    simp [cbOp, h0]
  · show cbiOp l f x = 0
    simp [cbiOp, h0]

/- English proof (translation)
Establish `hmem : ∀ Ψ : RadSp k r z z' π π', Ψ ∈ lcSub k r z z' π π' ↔ ∀ c ∈ OmX r, LCptAt Ψ c` using `fun Ψ => Iff.rfl`. Establish `hop : ∀ j, ∀ Ψ ∈ lcSub k r z z' π π', X.op l j Ψ ∈ lcSub k r z z' π π'`. Introduce `j Ψ hΨ`. Rewrite `hΨ`, the goal using `[hmem]`. Introduce `c hc`.

Take `⟨U', hU', hcU, K, hK, hKG, h0⟩` from `hΨ c hc`. Use `⟨U', hU', hcU, K, hK, hKG, fun c' hc' g hg hgK => ?_⟩` and prove the remaining obligations. Rewrite using `[X.op_apply]`. Use `show opL l j (fun c'' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c'' g) c' = 0`. Apply `opL_eq_zero_of_eventuallyEq_zero` to reduce the goal to its premises.

Use `filter_upwards [hU'.mem_nhds hc'] with c'' hc''`. Conclude with `h0 c'' hc'' g hg hgK`. Proceed by induction on `js with`. Consider the case `nil`. Introduce `Φ hΦ`.

Simplify `hΦ` using `[wOp]`. Consider the case `cons j js ih`. Introduce `Φ hΦ`. Use `show X.op l j (wOp X l js Φ) ∈ lcSub k r z z' π π'`. Conclude with `hop j _ (ih Φ hΦ)`.
-/
theorem jsl_wOp_lc (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) :
    ∀ Φ ∈ lcSub k r z z' π π', wOp X l js Φ ∈ lcSub k r z z' π π' := by
  have hmem : ∀ Ψ : RadSp k r z z' π π', Ψ ∈ lcSub k r z z' π π' ↔ ∀ c ∈ OmX r, LCptAt Ψ c :=
    fun Ψ => Iff.rfl
  have hop : ∀ j, ∀ Ψ ∈ lcSub k r z z' π π', X.op l j Ψ ∈ lcSub k r z z' π π' := by
    intro j Ψ hΨ
    rw [hmem] at hΨ ⊢
    intro c hc
    obtain ⟨U', hU', hcU, K, hK, hKG, h0⟩ := hΨ c hc
    refine ⟨U', hU', hcU, K, hK, hKG, fun c' hc' g hg hgK => ?_⟩
    rw [X.op_apply]
    show opL l j (fun c'' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c'' g) c' = 0
    apply opL_eq_zero_of_eventuallyEq_zero
    filter_upwards [hU'.mem_nhds hc'] with c'' hc''
    exact h0 c'' hc'' g hg hgK
  induction js with
  | nil =>
    intro Φ hΦ
    simpa [wOp] using hΦ
  | cons j js ih =>
    intro Φ hΦ
    show X.op l j (wOp X l js Φ) ∈ lcSub k r z z' π π'
    exact hop j _ (ih Φ hΦ)

/- English proof (translation)
Rewrite using `[B.hsInner, inner_self_eq_norm_sq_to_K]`. Simplify using `[norm_pow]`.
-/
theorem jsl_hsInner_self_norm (C : Wq →L[ℂ] Wp) : ‖B.hsInner C C‖ = ‖B.hsVec C‖ ^ 2 := by
  rw [B.hsInner, inner_self_eq_norm_sq_to_K]
  simp [norm_pow]

/- English proof (translation)
Establish `hlin : B.hsVec (∑ i, a i • A i) = ∑ i, a i • B.hsVec (A i)`. Express the relevant statement in the definitionally equal form `hsVecLin (∑ i, a i • A i) = ∑ i, a i • hsVecLin (A i)`. Simplify using `[map_sum, map_smul]`. Rewrite using `[jsl_hsInner_self_norm, hlin]`. Repeatedly rewrite using `[jsl_hsInner_self_norm]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `norm_sum_le _ _`. Use `_ ≤ (K : ℝ) * ∑ i, ‖a i • B.hsVec (A i)‖ ^ 2 := by`. Simplify using `using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i • B.hsVec (A i)‖)`. Use `_ = (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsVec (A i)‖ ^ 2 := by`.

Simplify using `[norm_smul, mul_pow]`.
-/
theorem jsl_hs_comb_le {K : ℕ} (a : Fin K → ℂ) (A : Fin K → (Wq →L[ℂ] Wp)) :
    ‖B.hsInner (∑ i, a i • A i) (∑ i, a i • A i)‖ ≤ (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsInner (A i) (A i)‖ := by
  have hlin : B.hsVec (∑ i, a i • A i) = ∑ i, a i • B.hsVec (A i) := by
    change hsVecLin (∑ i, a i • A i) = ∑ i, a i • hsVecLin (A i)
    simp [map_sum, map_smul]
  rw [jsl_hsInner_self_norm, hlin]
  simp_rw [jsl_hsInner_self_norm]
  calc ‖∑ i, a i • B.hsVec (A i)‖ ^ 2 ≤ (∑ i, ‖a i • B.hsVec (A i)‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ (K : ℝ) * ∑ i, ‖a i • B.hsVec (A i)‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i • B.hsVec (A i)‖)
    _ = (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsVec (A i)‖ ^ 2 := by
        simp [norm_smul, mul_pow]

/- English proof (translation)
Establish `hint : ∀ i, Integrable (fun g : Mt k r => ‖B.hsInner ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g)) ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖) μ` using `fun i => (int_lc μ hμ (hv i) (hv i) x).norm`. Rewrite using `[norm_pairAt_selfI]`. Simplify using `only [norm_pairAt_selfI]`. Combine the equalities or inequalities in the displayed calculation. Use `integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) ((integrable_finsetSum _ fun i _ => (hint i).const_mul _).const_mul _) (ae_of_all _ fun g => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[hx]`. Conclude with `jsl_hs_comb_le _ _`. Use `_ = _ := by`. Rewrite using `[integral_const_mul, integral_finsetSum _ fun i _ => (hint i).const_mul _]`.

Simplify using `only [integral_const_mul]`.
-/
theorem jsl_pairAt_comb_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {K : ℕ}
    (a : Fin K → ℂ) (u : RadSp k r z z' π π') (v : Fin K → RadSp k r z z' π π')
    (hv : ∀ i, v i ∈ lcSub k r z z' π π') (x : Fin r → ℂ)
    (hx : ∀ g, (u : Fn k r (Wq →L[ℂ] Wp)) x g = ∑ i, a i • (v i : Fn k r (Wq →L[ℂ] Wp)) x g) :
    ‖pairAt μ u u x‖ ≤ (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖pairAt μ (v i) (v i) x‖ := by
  have hint : ∀ i, Integrable (fun g : Mt k r => ‖B.hsInner ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
      ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖) μ := fun i => (int_lc μ hμ (hv i) (hv i) x).norm
  rw [norm_pairAt_selfI]
  simp only [norm_pairAt_selfI]
  calc ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
        ((u : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖ ∂μ
      ≤ ∫ g : Mt k r, (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsInner ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
        ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖ ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          ((integrable_finsetSum _ fun i _ => (hint i).const_mul _).const_mul _) (ae_of_all _ fun g => ?_)
        dsimp only
        rw [hx]; exact jsl_hs_comb_le _ _
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => (hint i).const_mul _]
        simp only [integral_const_mul]

/- English proof (translation)
Repeatedly rewrite using `[Complex.norm_real, Real.norm_of_nonneg (hf _)]`. Rewrite using `[integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg hf)]`.
-/
private theorem integral_norm_ofReal_eq_norm_integral_of_nonneg {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∫ a, ‖((f a : ℝ) : ℂ)‖ ∂ν = ‖∫ a, ((f a : ℝ) : ℂ) ∂ν‖ := by
  simp_rw [Complex.norm_real, Real.norm_of_nonneg (hf _)]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg hf)]

/- English proof (translation)
Establish `key : ∀ c' : Cf r i, wtI i c' * pairAt μ v v (glue i c c') = (((∏ l, ‖c' l‖ ^ (-2 : ℤ)) * ∫ g : Mt k r, ‖B.hsVec ((v : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))‖ ^ 2 ∂μ : ℝ) : ℂ)`. Introduce `c'`. Establish `hh : ∀ A : Wq →L[ℂ] Wp, B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ)` using `fun A => by`. Rewrite using `[B.hsInner, inner_self_eq_norm_sq_to_K]`. Use `norm_cast`.

Rewrite using `[wtI, pairAt]`. Repeatedly rewrite using `[hh]`. Rewrite using `[integral_complex_ofReal, Complex.ofReal_mul]`. Repeatedly rewrite using `[key]`. Apply `integral_norm_ofReal_eq_norm_integral_of_nonneg` to reduce the goal to its premises.

Introduce `c'`. Apply `mul_nonneg` to reduce the goal to its premises. Conclude with `Finset.prod_nonneg fun l _ => by positivity`. Conclude with `integral_nonneg fun g => by positivity`.
-/
theorem jsl_int_norm_self (μ : Measure (Mt k r)) (i : Fin (r + 1)) (v : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ∫ c' : Cf r i, ‖wtI i c' * pairAt μ v v (glue i c c')‖ =
      ‖∫ c' : Cf r i, wtI i c' * pairAt μ v v (glue i c c')‖ := by
  have key : ∀ c' : Cf r i, wtI i c' * pairAt μ v v (glue i c c') =
      (((∏ l, ‖c' l‖ ^ (-2 : ℤ)) *
        ∫ g : Mt k r, ‖B.hsVec ((v : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro c'
    have hh : ∀ A : Wq →L[ℂ] Wp, B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := fun A => by
      rw [B.hsInner, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [wtI, pairAt]
    simp_rw [hh]
    rw [integral_complex_ofReal, Complex.ofReal_mul]
  simp_rw [key]
  apply integral_norm_ofReal_eq_norm_integral_of_nonneg
  intro c'
  apply mul_nonneg
  · exact Finset.prod_nonneg fun l _ => by positivity
  · exact integral_nonneg fun g => by positivity

/- English proof (translation)
Unfold `glue`. Rewrite using `[dif_neg (by simp [Fin.val_succ])]`. Simplify using the standard rewrite rules.
-/
theorem jsl_glue_self (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  unfold glue
  rw [dif_neg (by simp [Fin.val_succ])]
  simp

end JSL

/- English proof (translation)
Introduce `hNF hRad Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc Ψ hΨ js t0 ht0`. Establish `hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ` using `hD.2.1`. Establish `: SFinite μ` using `sfinite_of_isHaarOn _ μ hμ`. Take `⟨hΨlc, s, ε, G, hε, hN, hG, hΨv⟩` from `hΨ`. Set `Wv : Module.End ℂ (RadSp P.k P.r z z' π π')` to `P5.mulOp (fun x => fsv s (x.1 l)) (P5.contDiff_fsv_coord l s) (fun _ _ _ _ _ _ => rfl)`.

Establish `hW : multiplicationOperator Wv (fun c _ => fsv s (c l))` using `P5.mulOp_isMulOp _ _ _`. Set `Wn : Module.End ℂ (RadSp P.k P.r z z' π π')` to `P5.mulOp (fun x => fsv (-s) (x.1 l)) (P5.contDiff_fsv_coord l (-s)) (fun _ _ _ _ _ _ => rfl)`. Establish `hWn : multiplicationOperator Wn (fun c _ => fsv (-s) (c l))` using `P5.mulOp_isMulOp _ _ _`. Establish `hΦlc : Wn Ψ ∈ lcSub P.k P.r z z' π π'` using `mul_lc hWn Ψ hΨlc`. Establish `hΦv : ∀ y ∈ DomR P.k P.r z z', ((Wn Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2`.

Introduce `y hy`. Rewrite using `[hWn Ψ y.1 y.2, hΨv y hy, smul_smul, fsv_neg_mul_fsv, one_smul]`. Establish `hΨeq : Wv (Wn Ψ) = Ψ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c' g`.

Use `show ((Wv (Wn Ψ) : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g`. Rewrite using `[hW (Wn Ψ) c' g, hWn Ψ c' g, smul_smul, fsv_mul_fsv_neg, one_smul]`. Take `⟨K, m, ab, hm, hab, hE⟩` from `hNF P.k P.r z z' Wp Wq π π' X l s Wv hW js`. Establish `hR : ∀ i, ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε', LevelSquareIntegrable μ l.succ (wOp X l (ab i) (Wn Ψ)) (Function.update c l t) ∧ ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ ≤ M` using `fun i => hRad Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl ε hε G hN hG (Wn Ψ) hΦlc hΦv c hc (ab i) (hab i) t0 ht0`. Use `choose ε' hε' M hM using hR`.

Establish `hac : ∀ i, ContinuousAt (fun t => m i t * fsv s t) t0` using `fun i => ((hm i).continuousAt (isOpen_compl_singleton.mem_nhds ht0)).mul (P5.contDiff_fsv s).continuous.continuousAt`. Establish `hev : ∀ᶠ t in 𝓝 t0, ∀ i, (LevelSquareIntegrable μ l.succ (wOp X l (ab i) (Wn Ψ)) (Function.update c l t) ∧ ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ ≤ M i) ∧ ‖m i t * fsv s t‖ ≤ ‖m i t0 * fsv s t0‖ + 1`. Rewrite using `[Filter.eventually_all]`. Introduce `i`. Use `(Filter.eventually_of_mem (Metric.ball_mem_nhds t0 (hε' i)) fun t ht => hM i t ht).and ?_` and prove the remaining obligations.

Conclude with `((hac i).norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun t ht => ht.le`. Take `⟨δ, hδ, hδP⟩` from `Metric.eventually_nhds_iff_ball.1 hev`. Use `⟨δ, hδ, (K : ℝ) * ∑ i, (‖m i t0 * fsv s t0‖ + 1) ^ 2 * M i, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hP` using `hδP t ht`. Establish `hvlc : ∀ i, wOp X l (ab i) (Wn Ψ) ∈ lcSub P.k P.r z z' π π'` using `fun i => jsl_wOp_lc X l (ab i) _ hΦlc`.

Establish `hx : ∀ (c' : Cf P.r l.succ) (g : Mx P.k P.r), (wOp X l js Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g = ∑ i, (m i t * fsv s t) • (wOp X l (ab i) (Wn Ψ) : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g`. Introduce `c' g`. Distinguish the cases in `hxo : glue l.succ (Function.update c l t) c' ∈ OmX P.r`. Establish `e` using `hE (Wn Ψ) _ hxo g`. Rewrite `e` using `[hΨeq, jsl_glue_self]`.

Conclude with `e`. Establish `h0 : ∀ w : RadSp P.k P.r z z' π π', (w : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g = 0` using `fun w => radSp_zero_off w (x := (glue l.succ (Function.update c l t) c', g)) (fun h => hxo h.1)`. Rewrite using `[h0]`. Simplify using `only [h0, smul_zero, Finset.sum_const_zero]`. Establish `hpt : ∀ c' : Cf P.r l.succ, ‖wtI l.succ c' * pairAt μ (wOp X l js Ψ) (wOp X l js Ψ) (glue l.succ (Function.update c l t) c')‖ ≤ (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖wtI l.succ c' * pairAt μ (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) (glue l.succ (Function.update c l t) c' …`.

Introduce `c'`. Use `jsl_pairAt_comb_le μ hμ (fun i => m i t * fsv s t) (wOp X l js Ψ) (fun i => wOp X l (ab i) (Wn Ψ)) hvlc _ (hx c')` as an intermediate fact. Rewrite using `[norm_mul]`. Use `(mul_le_mul_of_nonneg_left this (norm_nonneg _)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_left_comm, Finset.mul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [norm_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : Integrable (fun c' : Cf P.r l.succ => (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖wtI l.succ c' * pairAt μ (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) (glue l.succ (Function.update c l t) c')‖)` using `(integrable_finsetSum _ fun i _ => ((hP i).1.1.norm.const_mul _)).const_mul _`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `LevelSquareIntegrable`. Conclude with `hb.mono' ((wtI_measurable l.succ).aestronglyMeasurable.mul (pairAt_measI μ l.succ _ _ _).aestronglyMeasurable) (ae_of_all _ hpt)`. Establish `hfs : ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤ (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖`. Unfold `fs`.

Use `(norm_integral_le_integral_norm _).trans ?_` and prove the remaining obligations. Use `(integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hb (ae_of_all _ hpt)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[integral_const_mul, integral_finsetSum _ fun i _ => (hP i).1.1.norm.const_mul _]`. Simplify using `only [integral_const_mul, jsl_int_norm_self]`. Use `hfs.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _))` and prove the remaining obligations.

Conclude with `mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hP i).2 2) (hP i).1.2 (norm_nonneg _) (by positivity)`.
-/
theorem jSL2Loc_of : JSWordNF → JSRadLoc → SpectralL2Locality := by
  intro hNF hRad Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc Ψ hΨ js t0 ht0
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have : SFinite μ := sfinite_of_isHaarOn _ μ hμ
  obtain ⟨hΨlc, s, ε, G, hε, hN, hG, hΨv⟩ := hΨ

  let Wv : Module.End ℂ (RadSp P.k P.r z z' π π') :=
    P5.mulOp (fun x => fsv s (x.1 l)) (P5.contDiff_fsv_coord l s) (fun _ _ _ _ _ _ => rfl)
  have hW : multiplicationOperator Wv (fun c _ => fsv s (c l)) := P5.mulOp_isMulOp _ _ _
  let Wn : Module.End ℂ (RadSp P.k P.r z z' π π') :=
    P5.mulOp (fun x => fsv (-s) (x.1 l)) (P5.contDiff_fsv_coord l (-s)) (fun _ _ _ _ _ _ => rfl)
  have hWn : multiplicationOperator Wn (fun c _ => fsv (-s) (c l)) := P5.mulOp_isMulOp _ _ _
  have hΦlc : Wn Ψ ∈ lcSub P.k P.r z z' π π' := mul_lc hWn Ψ hΨlc
  have hΦv : ∀ y ∈ DomR P.k P.r z z', ((Wn Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2 := by
    intro y hy
    rw [hWn Ψ y.1 y.2, hΨv y hy, smul_smul, fsv_neg_mul_fsv, one_smul]
  have hΨeq : Wv (Wn Ψ) = Ψ := by
    apply Subtype.ext
    funext c' g
    show ((Wv (Wn Ψ) : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g
    rw [hW (Wn Ψ) c' g, hWn Ψ c' g, smul_smul, fsv_mul_fsv_neg, one_smul]

  obtain ⟨K, m, ab, hm, hab, hE⟩ := hNF P.k P.r z z' Wp Wq π π' X l s Wv hW js
  have hR : ∀ i, ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε',
      LevelSquareIntegrable μ l.succ (wOp X l (ab i) (Wn Ψ)) (Function.update c l t) ∧
        ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ ≤ M := fun i =>
    hRad Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl ε hε G hN hG (Wn Ψ) hΦlc hΦv c hc (ab i)
      (hab i) t0 ht0
  choose ε' hε' M hM using hR
  have hac : ∀ i, ContinuousAt (fun t => m i t * fsv s t) t0 := fun i =>
    ((hm i).continuousAt (isOpen_compl_singleton.mem_nhds ht0)).mul
      (P5.contDiff_fsv s).continuous.continuousAt
  have hev : ∀ᶠ t in 𝓝 t0, ∀ i, (LevelSquareIntegrable μ l.succ (wOp X l (ab i) (Wn Ψ)) (Function.update c l t) ∧
      ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ ≤ M i) ∧
      ‖m i t * fsv s t‖ ≤ ‖m i t0 * fsv s t0‖ + 1 := by
    rw [Filter.eventually_all]
    intro i
    refine (Filter.eventually_of_mem (Metric.ball_mem_nhds t0 (hε' i)) fun t ht => hM i t ht).and ?_
    exact ((hac i).norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun t ht => ht.le
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ, hδ, (K : ℝ) * ∑ i, (‖m i t0 * fsv s t0‖ + 1) ^ 2 * M i, fun t ht => ?_⟩
  have hP := hδP t ht
  have hvlc : ∀ i, wOp X l (ab i) (Wn Ψ) ∈ lcSub P.k P.r z z' π π' := fun i => jsl_wOp_lc X l (ab i) _ hΦlc

  have hx : ∀ (c' : Cf P.r l.succ) (g : Mx P.k P.r),
      (wOp X l js Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g =
        ∑ i, (m i t * fsv s t) •
          (wOp X l (ab i) (Wn Ψ) : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g := by
    intro c' g
    by_cases hxo : glue l.succ (Function.update c l t) c' ∈ OmX P.r
    · have e := hE (Wn Ψ) _ hxo g
      rw [hΨeq, jsl_glue_self] at e
      exact e
    · have h0 : ∀ w : RadSp P.k P.r z z' π π',
          (w : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g = 0 :=
        fun w => radSp_zero_off w (x := (glue l.succ (Function.update c l t) c', g)) (fun h => hxo h.1)
      rw [h0]
      simp only [h0, smul_zero, Finset.sum_const_zero]
  have hpt : ∀ c' : Cf P.r l.succ,
      ‖wtI l.succ c' * pairAt μ (wOp X l js Ψ) (wOp X l js Ψ) (glue l.succ (Function.update c l t) c')‖ ≤
        (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖wtI l.succ c' * pairAt μ (wOp X l (ab i) (Wn Ψ))
          (wOp X l (ab i) (Wn Ψ)) (glue l.succ (Function.update c l t) c')‖ := by
    intro c'
    have := jsl_pairAt_comb_le μ hμ (fun i => m i t * fsv s t) (wOp X l js Ψ) (fun i => wOp X l (ab i) (Wn Ψ))
      hvlc _ (hx c')
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left this (norm_nonneg _)).trans (le_of_eq ?_)
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [norm_mul]
    ring
  have hb : Integrable (fun c' : Cf P.r l.succ => (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 *
      ‖wtI l.succ c' * pairAt μ (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ))
        (glue l.succ (Function.update c l t) c')‖) :=
    (integrable_finsetSum _ fun i _ => ((hP i).1.1.norm.const_mul _)).const_mul _
  refine ⟨?_, ?_⟩
  · unfold LevelSquareIntegrable
    exact hb.mono' ((wtI_measurable l.succ).aestronglyMeasurable.mul
      (pairAt_measI μ l.succ _ _ _).aestronglyMeasurable) (ae_of_all _ hpt)
  · have hfs : ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤
        (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ := by
      unfold fs
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hb (ae_of_all _ hpt)).trans
        (le_of_eq ?_)
      rw [integral_const_mul, integral_finsetSum _ fun i _ => (hP i).1.1.norm.const_mul _]
      simp only [integral_const_mul, jsl_int_norm_self]
    refine hfs.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _))
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hP i).2 2) (hP i).1.2 (norm_nonneg _) (by positivity)

end Formalism.FourierDecayAlt.P.CutSE
