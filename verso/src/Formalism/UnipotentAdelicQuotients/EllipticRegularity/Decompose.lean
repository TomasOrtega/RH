import Formalism.UnipotentAdelicQuotients.EllRegStep

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

namespace Dec

variable {d : ℕ}

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hf`. Consider the case `cons j w ih => show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w f) x (ev j))`. Conclude with `(contDiff_infty_iff_fderiv.mp ih).2.clm_apply contDiff_const`.
-/
lemma contDiff_dw {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (w : List (Fin d)) : ContDiff ℝ ∞ (dw w f) := by
  induction w with
  | nil => exact hf
  | cons j w ih =>
    show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w f) x (ev j))
    exact (contDiff_infty_iff_fderiv.mp ih).2.clm_apply contDiff_const

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons j w ih`. Use function extensionality and compare the values at `x`. Use `show fderiv ℝ (dw w (fun y => f y + g y)) x (ev j) = fderiv ℝ (dw w f) x (ev j) + fderiv ℝ (dw w g) x (ev j)`.

Establish `h1` using `(contDiff_dw hf w).differentiable (by simp) x`. Establish `h2` using `(contDiff_dw hg w).differentiable (by simp) x`. Rewrite using `[ih]`. Use `first`. Consider the case `rw [show (fun y => dw w f y + dw w g y) = dw w f + dw w g from rfl, fderiv_add h1 h2]`.

Both sides reduce to the same expression. Consider the case `rw [fderiv_fun_add h1 h2]`. Both sides reduce to the same expression.
-/
lemma dw_add {f g : E d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List (Fin d)) :
    dw w (fun y => f y + g y) = fun y => dw w f y + dw w g y := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (dw w (fun y => f y + g y)) x (ev j) =
      fderiv ℝ (dw w f) x (ev j) + fderiv ℝ (dw w g) x (ev j)
    have h1 := (contDiff_dw hf w).differentiable (by simp) x
    have h2 := (contDiff_dw hg w).differentiable (by simp) x
    rw [ih]
    first
      | rw [show (fun y => dw w f y + dw w g y) = dw w f + dw w g from rfl, fderiv_add h1 h2]; rfl
      | rw [fderiv_fun_add h1 h2]; rfl

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons j w ih`. Use function extensionality and compare the values at `x`. Use `show fderiv ℝ (dw w (fun _ : E d => (0 : ℂ))) x (ev j) = 0`.

Rewrite using `[ih]`. Simplify using the standard rewrite rules.
-/
lemma dw_zero (w : List (Fin d)) : dw w (fun _ : E d => (0 : ℂ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (dw w (fun _ : E d => (0 : ℂ))) x (ev j) = 0
    rw [ih]
    simp

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons j w ih`. Use function extensionality and compare the values at `x`. Use `show fderiv ℝ (dw w (fun y => c * f y)) x (ev j) = c * fderiv ℝ (dw w f) x (ev j)`.

Establish `h1` using `(contDiff_dw hf w).differentiable (by simp) x`. Rewrite using `[ih]`. Use `first`. Consider the case `rw [fderiv_const_mul h1]`. Simplify using the standard rewrite rules.

Consider the case `rw [fderiv_fun_const_mul h1]`. Simplify using the standard rewrite rules. Consider the case `rw [show (fun y => c * dw w f y) = c • dw w f from rfl, fderiv_const_smul h1]`. Simplify using the standard rewrite rules.
-/
lemma dw_const_mul {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (w : List (Fin d)) :
    dw w (fun y => c * f y) = fun y => c * dw w f y := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (dw w (fun y => c * f y)) x (ev j) = c * fderiv ℝ (dw w f) x (ev j)
    have h1 := (contDiff_dw hf w).differentiable (by simp) x
    rw [ih]
    first
      | rw [fderiv_const_mul h1]; simp
      | rw [fderiv_fun_const_mul h1]; simp
      | rw [show (fun y => c * dw w f y) = c • dw w f from rfl, fderiv_const_smul h1]; simp

/- English proof (translation)
Simplify using `only [trOp]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Establish `e : (fun y => (b1 n w y + b2 n w y) * φ y) = fun y => b1 n w y * φ y + b2 n w y * φ y`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, dw_add ((h1 n w).mul hφ) ((h2 n w).mul hφ)]`. Simplify using `only [mul_add]`.
-/
lemma trOp_add (m : ℕ) (b1 b2 : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (h1 : ∀ n w, ContDiff ℝ ∞ (b1 n w)) (h2 : ∀ n w, ContDiff ℝ ∞ (b2 n w)) (hφ : ContDiff ℝ ∞ φ) (x : E d) :
    trOp m (fun n w y => b1 n w y + b2 n w y) φ x = trOp m b1 φ x + trOp m b2 φ x := by
  simp only [trOp]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (fun y => (b1 n w y + b2 n w y) * φ y) = fun y => b1 n w y * φ y + b2 n w y * φ y := by
    funext y
    ring
  rw [e, dw_add ((h1 n w).mul hφ) ((h2 n w).mul hφ)]
  simp only [mul_add]

/- English proof (translation)
Use `show Continuous (fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * φ y) x)`. Use `continuous_finset_sum _ fun n _ => continuous_finset_sum _ fun w _ => continuous_const.mul ?_` and prove the remaining obligations. Conclude with `(contDiff_dw ((hb n w).mul hφ) _).continuous`.
-/
lemma continuous_trOp (m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (hb : ∀ n w, ContDiff ℝ ∞ (b n w)) (hφ : ContDiff ℝ ∞ φ) : Continuous (trOp m b φ) := by
  show Continuous (fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
    (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * φ y) x)
  refine continuous_finset_sum _ fun n _ => continuous_finset_sum _ fun w _ => continuous_const.mul ?_
  exact (contDiff_dw ((hb n w).mul hφ) _).continuous

/- English proof (translation)
Establish `h1 : ContDiff ℝ ∞ (fun y : E d => ((inner ℝ y ξ : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)`. Conclude with `Complex.contDiff_exp.comp ((contDiff_const.mul h1).neg)`.
-/
lemma contDiff_eF (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by
  have h1 : ContDiff ℝ ∞ (fun y : E d => ((inner ℝ y ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const)
  exact Complex.contDiff_exp.comp ((contDiff_const.mul h1).neg)

/- English proof (translation)
Use `contDiff_iff_contDiffAt.mpr fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ U`. Conclude with `hg.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))`. Establish `hx' : x ∉ tsupport g` using `fun h => hx (hgU h)`. Establish `hev : g =ᶠ[𝓝 x] 0` using `by first`.

Consider the case `exact notMem_tsupport_iff_eventuallyEq.mp hx'`. Consider the case `exact not_mem_tsupport_iff_eventuallyEq.mp hx'`. Use `(contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with y hy`. Simplify using `[hy]`.
-/
lemma contDiff_mul_of_tsupport {U : Set (E d)} (hU : IsOpen U) {g f : E d → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgU : tsupport g ⊆ U) (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ (fun x => g x * f x) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x ∈ U
  · exact hg.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h => hx (hgU h)
    have hev : g =ᶠ[𝓝 x] 0 := by
      first
        | exact notMem_tsupport_iff_eventuallyEq.mp hx'
        | exact not_mem_tsupport_iff_eventuallyEq.mp hx'
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]

/- English proof (translation)
Establish `hχU' : ∀ x, x ∉ U → cut χ u =ᶠ[𝓝 x] 0`. Introduce `x hx`. Establish `hx' : x ∉ tsupport χ` using `fun h => hx (hχU h)`. Establish `hev : χ =ᶠ[𝓝 x] 0` using `by first`. Consider the case `exact notMem_tsupport_iff_eventuallyEq.mp hx'`.

Consider the case `exact not_mem_tsupport_iff_eventuallyEq.mp hx'`. Use `filter_upwards [hev] with y hy`. Simplify using `[cut, hy]`. Use `⟨continuous_iff_continuousAt.mpr fun x => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ U`.

Conclude with `(Complex.continuous_ofReal.comp hχ.continuous).continuousAt.mul (hu.continuousAt (hU.mem_nhds hx))`. Conclude with `continuousAt_const.congr (hχU' x hx).symm`. Conclude with `(hχc.comp_left Complex.ofReal_zero).mul_right`.
-/
lemma cut_cont {U : Set (E d)} (hU : IsOpen U) {u : E d → ℂ} (hu : ContinuousOn u U) {χ : E d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    Continuous (cut χ u) ∧ HasCompactSupport (cut χ u) := by
  have hχU' : ∀ x, x ∉ U → cut χ u =ᶠ[𝓝 x] 0 := by
    intro x hx
    have hx' : x ∉ tsupport χ := fun h => hx (hχU h)
    have hev : χ =ᶠ[𝓝 x] 0 := by
      first
        | exact notMem_tsupport_iff_eventuallyEq.mp hx'
        | exact not_mem_tsupport_iff_eventuallyEq.mp hx'
    filter_upwards [hev] with y hy
    simp [cut, hy]
  refine ⟨continuous_iff_continuousAt.mpr fun x => ?_, ?_⟩
  · by_cases hx : x ∈ U
    · exact (Complex.continuous_ofReal.comp hχ.continuous).continuousAt.mul
        (hu.continuousAt (hU.mem_nhds hx))
    · exact continuousAt_const.congr (hχU' x hx).symm
  · exact (hχc.comp_left Complex.ofReal_zero).mul_right

/- English proof (translation)
Conclude with `(tsupport_mul_subset_left).trans (tsupport_comp_subset Complex.ofReal_zero χ)`.
-/
lemma tsupport_cut (χ : E d → ℝ) (u : E d → ℂ) : tsupport (cut χ u) ⊆ tsupport χ := by
  exact (tsupport_mul_subset_left).trans (tsupport_comp_subset Complex.ofReal_zero χ)

/- English proof (translation)
Establish `hcont : Continuous (fun x : E d => r⁻¹ • (x - x0))` using `(continuous_id.sub continuous_const).const_smul r⁻¹`. Establish `hnorm : ∀ x : E d, ‖r⁻¹ • (x - x0)‖ = r⁻¹ * dist x x0`. Introduce `x`. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), dist_eq_norm]`. Establish `h3 : tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆ ball x0 (2 * r)`.

Establish `hsub : tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆ (fun x : E d => r⁻¹ • (x - x0)) ⁻¹' tsupport ψ0`. Apply `closure_minimal _ ((isClosed_tsupport ψ0).preimage hcont)` to reduce the goal to its premises. Introduce `x hx`. Apply `subset_tsupport` to reduce the goal to its premises. Introduce `h0`.

Apply `hx` to reduce the goal to its premises. Simplify using `[h0]`. Use `hsub.trans fun x hx => ?_` and prove the remaining obligations. Establish `h2 : r⁻¹ • (x - x0) ∈ ball (0 : E d) 2` using `hψs hx`. Rewrite `h2` using `[mem_ball_zero_iff, hnorm]`.

Rewrite using `[mem_ball]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Complex.ofRealCLM.contDiff.comp (hψ.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)), ?_, h3, ?_⟩` and prove the remaining obligations. Conclude with `IsCompact.of_isClosed_subset (isCompact_closedBall x0 (2 * r)) (isClosed_tsupport _) (h3.trans ball_subset_closedBall)`. Introduce `x hx`.

Establish `h1 : r⁻¹ • (x - x0) ∈ ball (0 : E d) 1`. Rewrite using `[mem_ball_zero_iff, hnorm]`. Rewrite `hx` using `[mem_ball]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hψ1 _ h1]`.

Simplify using the standard rewrite rules.
-/
lemma psi_props (x0 : E d) (ψ0 : E d → ℝ) (r : ℝ) (hψ : ContDiff ℝ ∞ ψ0) (hψc : HasCompactSupport ψ0)
    (hψ1 : ∀ y ∈ ball (0 : E d) 1, ψ0 y = 1) (hψs : tsupport ψ0 ⊆ ball 0 2) (hr : 0 < r) :
    ContDiff ℝ ∞ (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ∧
    HasCompactSupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ∧
    tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆ ball x0 (2 * r) ∧
    ∀ x ∈ ball x0 r, ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) = 1 := by
  have hcont : Continuous (fun x : E d => r⁻¹ • (x - x0)) :=
    (continuous_id.sub continuous_const).const_smul r⁻¹
  have hnorm : ∀ x : E d, ‖r⁻¹ • (x - x0)‖ = r⁻¹ * dist x x0 := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), dist_eq_norm]
  have h3 : tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆ ball x0 (2 * r) := by
    have hsub : tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆
        (fun x : E d => r⁻¹ • (x - x0)) ⁻¹' tsupport ψ0 := by
      apply closure_minimal _ ((isClosed_tsupport ψ0).preimage hcont)
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
    refine hsub.trans fun x hx => ?_
    have h2 : r⁻¹ • (x - x0) ∈ ball (0 : E d) 2 := hψs hx
    rw [mem_ball_zero_iff, hnorm] at h2
    rw [mem_ball]
    calc dist x x0 = r * (r⁻¹ * dist x x0) := by field_simp
      _ < r * 2 := by gcongr
      _ = 2 * r := by ring
  refine ⟨Complex.ofRealCLM.contDiff.comp (hψ.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)),
    ?_, h3, ?_⟩
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall x0 (2 * r)) (isClosed_tsupport _)
      (h3.trans ball_subset_closedBall)
  · intro x hx
    have h1 : r⁻¹ • (x - x0) ∈ ball (0 : E d) 1 := by
      rw [mem_ball_zero_iff, hnorm]
      rw [mem_ball] at hx
      calc r⁻¹ * dist x x0 < r⁻¹ * r := by gcongr
        _ = 1 := inv_mul_cancel₀ hr.ne'
    rw [hψ1 _ h1]
    simp

/- English proof (translation)
Rewrite using `[List.map_ofFn, List.prod_ofFn]`. Simplify using `only [Function.comp_def]`. Rewrite using `[Finset.prod_neg, Finset.card_univ, Fintype.card_fin]`. Both sides reduce to the same expression.
-/
lemma prod_neg_eq (n : ℕ) (w : Fin n → Fin d) (ξ : E d) :
    ((List.ofFn w).map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod = (-1 : ℂ) ^ n * mono w ξ := by
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_def]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  rfl

end Dec

/- English proof (translation)
Introduce `hPF hDw hFP hPL hWF d ι _ P U u hyp x0 ψ0 r hψ hψc hψ1 hψs hr hball χ χ' hχ hχc hχs hχ' hχ'c hχ's hχχ' i`. Take `⟨hUo, hA, -, hu, -⟩` from `id hyp`. Establish `hχU : tsupport χ ⊆ U` using `hχs.trans ((ball_subset_ball (by linarith)).trans hball)`. Take `⟨c, hc, hcw⟩` from `hWF d ι P U u hyp i χ χ' hχ hχc hχU hχ' hχ'c hχ's hχχ'`. Take `⟨hψC, hψH, hψT, hψ1'⟩` from `Dec.psi_props x0 ψ0 r hψ hψc hψ1 hψs hr`.

Take `⟨hgc, hgs⟩` from `Dec.cut_cont hUo hu hχ hχc hχU`. Take `⟨hg'c, hg's⟩` from `Dec.cut_cont hUo hu hχ' hχ'c hχ's`. Use `set m := P.ord i with hm`. Establish `hψU` using `hψT.trans hball`. Set `lo : (n : ℕ) → (Fin n → Fin d) → E d → ℂ` to `fun n w x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (P.a i n w x - if n = m then P.a i n w x0 else 0)`.

Set `b2 : (n : ℕ) → (Fin n → Fin d) → E d → ℂ` to `fun n w _ => if n = m then P.a i n w x0 else 0`. Establish `hlo : ∀ n w, ContDiff ℝ ∞ (lo n w) ∧ HasCompactSupport (lo n w)` using `fun n w => ⟨Dec.contDiff_mul_of_tsupport hUo hψC hψU ((hA i n w).sub contDiffOn_const), hψH.mul_right⟩`. Establish `hb2 : ∀ n w, ContDiff ℝ ∞ (b2 n w)` using `fun n w => contDiff_const`. Use `⟨lo, c, hlo, hc, fun ξ => ?_⟩` and prove the remaining obligations. Establish `hφ` using `Dec.contDiff_eF ξ`.

Establish `hterm : ∀ n (w : Fin n → Fin d), ∫ y, cut χ' u y * c n w y * dw (List.ofFn w) (eF ξ) y = (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) (𝓕 (cut χ' u)) ξ`. Introduce `n w`. Establish `hpf` using `hPF d 0 (fun _ _ => c n w) (cut χ' u) (fun _ _ => hc n w) hg'c hg's ξ`. Establish `htr0 : ∀ y, trOp 0 (fun _ _ => c n w) (eF ξ) y = c n w y * eF ξ y`. Introduce `y`.

Simplify using `[trOp, dw]`. Establish `hmono0 : ∀ (w' : Fin 0 → Fin d) (η : E d), mono w' η = 1`. Introduce `w' η`. Simplify using `[mono]`. Simplify using `only [htr0] at hpf`.

Establish `e1 : (fun y => cut χ' u y * c n w y * dw (List.ofFn w) (eF ξ) y) = fun y => ((-1 : ℂ) ^ n * mono w ξ) * (cut χ' u y * (c n w y * eF ξ y))`. Use function extensionality and compare the values at `y`. Simplify using `only [hDw d ξ (List.ofFn w), Dec.prod_neg_eq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, integral_const_mul, hpf]`.

Simplify using `[hmono0]`. Establish `hR : ∫ y, cut χ u y * P.tr i (eF ξ) y = ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) (𝓕 (cut χ' u)) ξ`. Rewrite using `[hcw ξ]`. Conclude with `Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => hterm n w`. Establish `hloc` using `hPL d m (P.a i) (fun n w y => lo n w y + b2 n w y) (cut χ u) (eF ξ) (ball x0 r) isOpen_ball ((Dec.tsupport_cut χ u).trans hχs) (by`.

Introduce `n w x hx`. Establish `h1` using `hψ1' x hx`. Simplify using `only [lo, b2, h1]`. Apply the tactic sequence `split_ifs <;> ring)`. Establish `hsplit : ∀ y, trOp m (fun n w y => lo n w y + b2 n w y) (eF ξ) y = trOp m lo (eF ξ) y + trOp m b2 (eF ξ) y` using `fun y => Dec.trOp_add m lo b2 (eF ξ) (fun n w => (hlo n w).1) hb2 hφ y`.

Establish `hb2e : ∀ y, trOp m b2 (eF ξ) y = (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * eF ξ y`. Introduce `y`. Simplify using `only [trOp]`. Rewrite using `[Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Simplify using `only [b2, eq_self_iff_true, if_true]`. Rewrite using `[Dec.dw_const_mul hφ, hDw d ξ (List.ofFn w), Dec.prod_neg_eq]`. Use `beta_reduce`. Establish `hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1`. Rewrite using `[← mul_pow]`.

Evaluate the numerical expressions. Take the linear combination `(P.a i m w x0 * mono w ξ * eF ξ y) * hsq`. Introduce `n hn`. Establish `hne : n ≠ m` using `(Finset.mem_range.mp hn).ne`. Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations.

Simplify using `only [b2, if_neg hne, zero_mul]`. Rewrite using `[Dec.dw_zero]`. Simplify using the standard rewrite rules. Establish `hint1 : Integrable (fun y => cut χ u y * trOp m lo (eF ξ) y)` using `(hgc.mul (Dec.continuous_trOp m lo (eF ξ) (fun n w => (hlo n w).1) hφ)).integrable_of_hasCompactSupport hgs.mul_right`. Establish `hint2 : Integrable (fun y => cut χ u y * trOp m b2 (eF ξ) y)` using `(hgc.mul (Dec.continuous_trOp m b2 (eF ξ) hb2 hφ)).integrable_of_hasCompactSupport hgs.mul_right`.

Establish `hconst : ∫ y, cut χ u y * trOp m b2 (eF ξ) y = (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * 𝓕 (cut χ u) ξ`. Repeatedly rewrite using `[hb2e]`. Rewrite using `[← hFP d (cut χ u) hgc hgs ξ, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∫ y, cut χ u y * P.tr i (eF ξ) y = (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * 𝓕 (cut χ u) ξ + ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, conv (𝓕 (lo n w)) (fun η => mono w η * 𝓕 (cut χ u) η) ξ`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `y`.

Rewrite using `[hsplit y, mul_add]`. Use `_ = (∫ y, cut χ u y * trOp m lo (eF ξ) y) + ∫ y, cut χ u y * trOp m b2 (eF ξ) y := integral_add hint1 hint2`. Use `_ = _ := by`. Rewrite using `[hPF d m lo (cut χ u) hlo hgc hgs ξ, hconst, add_comm]`. Establish `hlom : ∀ w : Fin m → Fin d, lo m w = fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (P.a i m w x - P.a i m w x0)`.

Introduce `w`. Use function extensionality and compare the values at `x`. Simplify using `only [lo, eq_self_iff_true, if_true]`. Rewrite using `[← hR, key, Finset.sum_range_succ]`. Simplify using `only [hlom]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem frozenDecompositionOfParts : DecomposeOf := by
  intro hPF hDw hFP hPL hWF d ι _ P U u hyp x0 ψ0 r hψ hψc hψ1 hψs hr hball χ χ' hχ hχc hχs
    hχ' hχ'c hχ's hχχ' i
  obtain ⟨hUo, hA, -, hu, -⟩ := id hyp
  have hχU : tsupport χ ⊆ U := hχs.trans ((ball_subset_ball (by linarith)).trans hball)
  obtain ⟨c, hc, hcw⟩ := hWF d ι P U u hyp i χ χ' hχ hχc hχU hχ' hχ'c hχ's hχχ'
  obtain ⟨hψC, hψH, hψT, hψ1'⟩ := Dec.psi_props x0 ψ0 r hψ hψc hψ1 hψs hr
  obtain ⟨hgc, hgs⟩ := Dec.cut_cont hUo hu hχ hχc hχU
  obtain ⟨hg'c, hg's⟩ := Dec.cut_cont hUo hu hχ' hχ'c hχ's
  set m := P.ord i with hm
  have hψU := hψT.trans hball
  let lo : (n : ℕ) → (Fin n → Fin d) → E d → ℂ := fun n w x =>
    ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (P.a i n w x - if n = m then P.a i n w x0 else 0)
  let b2 : (n : ℕ) → (Fin n → Fin d) → E d → ℂ := fun n w _ => if n = m then P.a i n w x0 else 0
  have hlo : ∀ n w, ContDiff ℝ ∞ (lo n w) ∧ HasCompactSupport (lo n w) := fun n w =>
    ⟨Dec.contDiff_mul_of_tsupport hUo hψC hψU ((hA i n w).sub contDiffOn_const), hψH.mul_right⟩
  have hb2 : ∀ n w, ContDiff ℝ ∞ (b2 n w) := fun n w => contDiff_const
  refine ⟨lo, c, hlo, hc, fun ξ => ?_⟩
  have hφ := Dec.contDiff_eF ξ
  have hterm : ∀ n (w : Fin n → Fin d), ∫ y, cut χ' u y * c n w y * dw (List.ofFn w) (eF ξ) y =
      (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) (𝓕 (cut χ' u)) ξ := by
    intro n w
    have hpf := hPF d 0 (fun _ _ => c n w) (cut χ' u) (fun _ _ => hc n w) hg'c hg's ξ
    have htr0 : ∀ y, trOp 0 (fun _ _ => c n w) (eF ξ) y = c n w y * eF ξ y := by
      intro y
      simp [trOp, dw]
    have hmono0 : ∀ (w' : Fin 0 → Fin d) (η : E d), mono w' η = 1 := by
      intro w' η
      simp [mono]
    simp only [htr0] at hpf
    have e1 : (fun y => cut χ' u y * c n w y * dw (List.ofFn w) (eF ξ) y) =
        fun y => ((-1 : ℂ) ^ n * mono w ξ) * (cut χ' u y * (c n w y * eF ξ y)) := by
      funext y
      simp only [hDw d ξ (List.ofFn w), Dec.prod_neg_eq]
      ring
    rw [e1, integral_const_mul, hpf]
    simp [hmono0]
  have hR : ∫ y, cut χ u y * P.tr i (eF ξ) y = ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d,
      (-1 : ℂ) ^ n * mono w ξ * conv (𝓕 (c n w)) (𝓕 (cut χ' u)) ξ := by
    rw [hcw ξ]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => hterm n w
  have hloc := hPL d m (P.a i) (fun n w y => lo n w y + b2 n w y) (cut χ u) (eF ξ) (ball x0 r)
    isOpen_ball ((Dec.tsupport_cut χ u).trans hχs) (by
      intro n w x hx
      have h1 := hψ1' x hx
      simp only [lo, b2, h1]
      split_ifs <;> ring)
  have hsplit : ∀ y, trOp m (fun n w y => lo n w y + b2 n w y) (eF ξ) y =
      trOp m lo (eF ξ) y + trOp m b2 (eF ξ) y :=
    fun y => Dec.trOp_add m lo b2 (eF ξ) (fun n w => (hlo n w).1) hb2 hφ y
  have hb2e : ∀ y, trOp m b2 (eF ξ) y =
      (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * eF ξ y := by
    intro y
    simp only [trOp]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Finset.sum_mul]
    · refine Finset.sum_congr rfl fun w _ => ?_
      simp only [b2, eq_self_iff_true, if_true]
      rw [Dec.dw_const_mul hφ, hDw d ξ (List.ofFn w), Dec.prod_neg_eq]
      beta_reduce
      have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by
        rw [← mul_pow]
        norm_num
      linear_combination (P.a i m w x0 * mono w ξ * eF ξ y) * hsq
    · intro n hn
      have hne : n ≠ m := (Finset.mem_range.mp hn).ne
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [b2, if_neg hne, zero_mul]
      rw [Dec.dw_zero]
      simp
  have hint1 : Integrable (fun y => cut χ u y * trOp m lo (eF ξ) y) :=
    (hgc.mul (Dec.continuous_trOp m lo (eF ξ) (fun n w => (hlo n w).1) hφ)).integrable_of_hasCompactSupport
      hgs.mul_right
  have hint2 : Integrable (fun y => cut χ u y * trOp m b2 (eF ξ) y) :=
    (hgc.mul (Dec.continuous_trOp m b2 (eF ξ) hb2 hφ)).integrable_of_hasCompactSupport hgs.mul_right
  have hconst : ∫ y, cut χ u y * trOp m b2 (eF ξ) y =
      (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * 𝓕 (cut χ u) ξ := by
    simp_rw [hb2e]
    rw [← hFP d (cut χ u) hgc hgs ξ, ← integral_const_mul]
    congr 1
    funext y
    ring
  have key : ∫ y, cut χ u y * P.tr i (eF ξ) y =
      (∑ w : Fin m → Fin d, P.a i m w x0 * mono w ξ) * 𝓕 (cut χ u) ξ +
        ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          conv (𝓕 (lo n w)) (fun η => mono w η * 𝓕 (cut χ u) η) ξ := by
    calc ∫ y, cut χ u y * P.tr i (eF ξ) y
        = ∫ y, cut χ u y * trOp m (fun n w y => lo n w y + b2 n w y) (eF ξ) y := hloc
      _ = ∫ y, (cut χ u y * trOp m lo (eF ξ) y + cut χ u y * trOp m b2 (eF ξ) y) := by
          congr 1
          funext y
          rw [hsplit y, mul_add]
      _ = (∫ y, cut χ u y * trOp m lo (eF ξ) y) + ∫ y, cut χ u y * trOp m b2 (eF ξ) y :=
          integral_add hint1 hint2
      _ = _ := by
          rw [hPF d m lo (cut χ u) hlo hgc hgs ξ, hconst, add_comm]
  have hlom : ∀ w : Fin m → Fin d,
      lo m w = fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) * (P.a i m w x - P.a i m w x0) := by
    intro w
    funext x
    simp only [lo, eq_self_iff_true, if_true]
  rw [← hR, key, Finset.sum_range_succ]
  simp only [hlom]
  ring

end

end ZetaZeros.D.EllReg
