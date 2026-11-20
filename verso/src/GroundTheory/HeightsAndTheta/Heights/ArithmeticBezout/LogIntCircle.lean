import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace LogInt

/- English proof (translation)
Use `set G : ℝ → ℝ := fun θ => Real.log ‖P.eval (circleMap 0 1 θ)‖ with hGdef`. Establish `hP : P ≠ 0` using `fun h => hd0 (by simp [h])`. Establish `h2pi : (0 : ℝ) ≤ 2 * Real.pi` using `by positivity`. Establish `hii : IntervalIntegrable G volume 0 (2 * Real.pi)` using `Polynomial.intervalIntegrable_mahlerMeasure P`. Establish `hint : IntegrableOn G (Ioc 0 (2 * Real.pi))` using `(intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi).mp hii`.

Rewrite using `[← ofReal_integral_norm_eq_lintegral_enorm hint]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Use `set L := Real.log (max M 1) with hL`. Establish `hpos : ∀ θ, G θ ≤ L`. Introduce `θ`.

Distinguish the cases in `h0 : ‖P.eval (circleMap 0 1 θ)‖ = 0`. Simplify using `only [hGdef, h0, Real.log_zero]`. Conclude with `Real.log_nonneg (le_max_right _ _)`. Conclude with `Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) ((hM θ).trans (le_max_left _ _))`. Establish `hnorm : ∀ θ, ‖G θ‖ = 2 * max (G θ) 0 - G θ`.

Introduce `θ`. Rewrite using `[Real.norm_eq_abs]`. Break down `le_total (G θ) 0 with h | h` into its components or cases. Rewrite using `[abs_of_nonpos h, max_eq_right h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[abs_of_nonneg h, max_eq_left h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmaxint : IntegrableOn (fun θ => max (G θ) 0) (Ioc 0 (2 * Real.pi))` using `hint.pos_part`. Establish `e1 : ∫ θ in Ioc 0 (2 * Real.pi), ‖G θ‖ = 2 * (∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0) - ∫ θ in Ioc 0 (2 * Real.pi), G θ`. Rewrite using `[show (fun θ => ‖G θ‖) = fun θ => 2 * max (G θ) 0 - G θ from funext hnorm]`.

Rewrite using `[integral_sub (hmaxint.const_mul 2) hint, integral_const_mul]`. Establish `e2 : ∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0 ≤ 2 * Real.pi * L`. Establish `: ∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0 ≤ ∫ θ in Ioc 0 (2 * Real.pi), L`. Use `setIntegral_mono_on hmaxint (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc ?_` and prove the remaining obligations. Introduce `θ _`.

Conclude with `max_le (hpos θ) (Real.log_nonneg (le_max_right _ _))`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[setIntegral_const]`. Simplify using `[Measure.real, Real.volume_Ioc, Real.pi_pos.le, smul_eq_mul]`. Establish `e3 : ∫ θ in Ioc 0 (2 * Real.pi), G θ = 2 * Real.pi * P.logMahlerMeasure`.

Rewrite using `[Polynomial.logMahlerMeasure_def, Real.circleAverage_def, ← intervalIntegral.integral_of_le h2pi]`. Rewrite using `[smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]`. Establish `e4 : Real.log ‖P.coeff d0‖ - D * Real.log 2 ≤ P.logMahlerMeasure`. Establish `hc` using `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure d0 P`. Establish `hm` using `Polynomial.mahlerMeasure_pos_of_ne_zero hP`.

Establish `hch : ((P.natDegree.choose d0 : ℕ) : ℝ) ≤ 2 ^ D`. Use `(Nat.choose_le_two_pow P.natDegree d0).trans (Nat.pow_le_pow_right (by norm_num) hD)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `h1 : ‖P.coeff d0‖ ≤ 2 ^ D * P.mahlerMeasure` using `hc.trans (mul_le_mul_of_nonneg_right hch hm.le)`. Establish `h2` using `Real.log_le_log (norm_pos_iff.mpr hd0) h1`.

Rewrite `h2` using `[Real.log_mul (by positivity) hm.ne', Real.log_pow]`. Rewrite using `[Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e1, e3]`. Establish `h5` using `neg_abs_le (Real.log ‖P.coeff d0‖)`.

Establish `h6` using `mul_le_mul_of_nonneg_left e4 h2pi`. Establish `h7` using `mul_le_mul_of_nonneg_left h5 h2pi`. Combine the linear relations using `[e2, h6, h7]`.
-/
theorem lintegral_abs_log_circle_le (P : Polynomial ℂ) (D d0 : ℕ) (M : ℝ)
    (hD : P.natDegree ≤ D) (hd0 : P.coeff d0 ≠ 0)
    (hM : ∀ θ : ℝ, ‖P.eval (circleMap 0 1 θ)‖ ≤ M) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖P.eval (circleMap 0 1 θ)‖‖ₑ ≤
      ENNReal.ofReal (4 * Real.pi * Real.log (max M 1) + 2 * Real.pi * D * Real.log 2 +
        2 * Real.pi * |Real.log ‖P.coeff d0‖|) := by
  set G : ℝ → ℝ := fun θ => Real.log ‖P.eval (circleMap 0 1 θ)‖ with hGdef
  have hP : P ≠ 0 := fun h => hd0 (by simp [h])
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hii : IntervalIntegrable G volume 0 (2 * Real.pi) := Polynomial.intervalIntegrable_mahlerMeasure P
  have hint : IntegrableOn G (Ioc 0 (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi).mp hii
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
  apply ENNReal.ofReal_le_ofReal
  set L := Real.log (max M 1) with hL
  have hpos : ∀ θ, G θ ≤ L := by
    intro θ
    by_cases h0 : ‖P.eval (circleMap 0 1 θ)‖ = 0
    · simp only [hGdef, h0, Real.log_zero]; exact Real.log_nonneg (le_max_right _ _)
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
        ((hM θ).trans (le_max_left _ _))
  have hnorm : ∀ θ, ‖G θ‖ = 2 * max (G θ) 0 - G θ := by
    intro θ; rw [Real.norm_eq_abs]; rcases le_total (G θ) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  have hmaxint : IntegrableOn (fun θ => max (G θ) 0) (Ioc 0 (2 * Real.pi)) := hint.pos_part
  have e1 : ∫ θ in Ioc 0 (2 * Real.pi), ‖G θ‖ =
      2 * (∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0) - ∫ θ in Ioc 0 (2 * Real.pi), G θ := by
    rw [show (fun θ => ‖G θ‖) = fun θ => 2 * max (G θ) 0 - G θ from funext hnorm]
    rw [integral_sub (hmaxint.const_mul 2) hint, integral_const_mul]
  have e2 : ∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0 ≤ 2 * Real.pi * L := by
    have : ∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0 ≤ ∫ θ in Ioc 0 (2 * Real.pi), L := by
      refine setIntegral_mono_on hmaxint (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc ?_
      intro θ _
      exact max_le (hpos θ) (Real.log_nonneg (le_max_right _ _))
    refine this.trans (le_of_eq ?_)
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioc, Real.pi_pos.le, smul_eq_mul]
  have e3 : ∫ θ in Ioc 0 (2 * Real.pi), G θ = 2 * Real.pi * P.logMahlerMeasure := by
    rw [Polynomial.logMahlerMeasure_def, Real.circleAverage_def, ← intervalIntegral.integral_of_le h2pi]
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have e4 : Real.log ‖P.coeff d0‖ - D * Real.log 2 ≤ P.logMahlerMeasure := by
    have hc := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure d0 P
    have hm := Polynomial.mahlerMeasure_pos_of_ne_zero hP
    have hch : ((P.natDegree.choose d0 : ℕ) : ℝ) ≤ 2 ^ D := by
      have := (Nat.choose_le_two_pow P.natDegree d0).trans (Nat.pow_le_pow_right (by norm_num) hD)
      exact_mod_cast this
    have h1 : ‖P.coeff d0‖ ≤ 2 ^ D * P.mahlerMeasure :=
      hc.trans (mul_le_mul_of_nonneg_right hch hm.le)
    have h2 := Real.log_le_log (norm_pos_iff.mpr hd0) h1
    rw [Real.log_mul (by positivity) hm.ne', Real.log_pow] at h2
    rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
    linarith
  rw [e1, e3]
  have h5 := neg_abs_le (Real.log ‖P.coeff d0‖)
  have h6 := mul_le_mul_of_nonneg_left e4 h2pi
  have h7 := mul_le_mul_of_nonneg_left h5 h2pi
  linarith [e2, h6, h7]

/- English proof (translation)
Distinguish the cases in `h : ∃ θ0, circleMap 0 1 θ0 = ρ`. Take `⟨θ0, h0⟩` from `h`. Use `(Set.countable_range (fun n : ℤ => θ0 + n * (2 * Real.pi))).mono ?_` and prove the remaining obligations. Introduce `θ hθ`. Simplify using `only [mem_ofPred_eq, circleMap_zero, Complex.ofReal_one, one_mul] at hθ h0`.

Rewrite `hθ` using `[← h0, Complex.exp_eq_exp_iff_exists_int]`. Take `⟨n, hn⟩` from `hθ`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `congrArg Complex.im hn` as an intermediate fact. Simplify using `at this`.

Simplify using `only`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at h`. Simplify using `[h]`.
-/
theorem countable_circleMap_eq (ρ : ℂ) : {θ : ℝ | circleMap 0 1 θ = ρ}.Countable := by
  by_cases h : ∃ θ0, circleMap 0 1 θ0 = ρ
  · obtain ⟨θ0, h0⟩ := h
    refine (Set.countable_range (fun n : ℤ => θ0 + n * (2 * Real.pi))).mono ?_
    intro θ hθ
    simp only [mem_ofPred_eq, circleMap_zero, Complex.ofReal_one, one_mul] at hθ h0
    rw [← h0, Complex.exp_eq_exp_iff_exists_int] at hθ
    obtain ⟨n, hn⟩ := hθ
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    simp only
    linarith
  · push Not at h
    simp [h]

/- English proof (translation)
Establish `hsub : {θ : ℝ | P.eval (circleMap 0 1 θ) = 0} ⊆ ⋃ ρ ∈ P.roots.toFinset, {θ : ℝ | circleMap 0 1 θ = ρ}`. Introduce `θ hθ`. Simplify using `only [mem_iUnion, mem_ofPred_eq]`. Conclude with `⟨circleMap 0 1 θ, by`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hP]`.

Conclude with `hθ, rfl⟩`. Conclude with `((P.roots.toFinset.countable_toSet).biUnion fun ρ _ => countable_circleMap_eq ρ).mono hsub`.
-/
theorem countable_eval_circleMap_eq_zero (P : Polynomial ℂ) (hP : P ≠ 0) :
    {θ : ℝ | P.eval (circleMap 0 1 θ) = 0}.Countable := by
  have hsub : {θ : ℝ | P.eval (circleMap 0 1 θ) = 0} ⊆
      ⋃ ρ ∈ P.roots.toFinset, {θ : ℝ | circleMap 0 1 θ = ρ} := by
    intro θ hθ
    simp only [mem_iUnion, mem_ofPred_eq]
    exact ⟨circleMap 0 1 θ, by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]; exact hθ, rfl⟩
  exact ((P.roots.toFinset.countable_toSet).biUnion fun ρ _ => countable_circleMap_eq ρ).mono hsub

/- English proof (translation)
Establish `h1 : ∀ θ, ∫⁻ u in S, G (R θ u) ∂μ = ∫⁻ u in S, G u ∂μ`. Introduce `θ`. Use `(hpres θ).setLIntegral_comp_preimage hS hG` as an intermediate fact. Rewrite `this` using `[hinv θ]`. Then use the resulting hypothesis. Rewrite using `[lintegral_lintegral_swap]`.

Repeatedly rewrite using `[h1]`. Rewrite using `[setLIntegral_const]`. Simplify using `[Real.volume_Ioc, mul_comm]`. Conclude with `(hG.comp (hR.comp measurable_swap)).aemeasurable`.
-/
theorem setLIntegral_rot {V : Type*} [MeasurableSpace V] (μ : Measure V) [SFinite μ]
    (S : Set V) (hS : MeasurableSet S) (R : ℝ → V → V) (hR : Measurable (Function.uncurry R))
    (hpres : ∀ θ, MeasurePreserving (R θ) μ μ) (hinv : ∀ θ, R θ ⁻¹' S = S)
    (G : V → ENNReal) (hG : Measurable G) :
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ u in S, G u ∂μ =
      ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), G (R θ u)) ∂μ := by
  have h1 : ∀ θ, ∫⁻ u in S, G (R θ u) ∂μ = ∫⁻ u in S, G u ∂μ := by
    intro θ
    have := (hpres θ).setLIntegral_comp_preimage hS hG
    rwa [hinv θ] at this
  rw [lintegral_lintegral_swap]
  · simp_rw [h1]
    rw [setLIntegral_const]
    simp [Real.volume_Ioc, mul_comm]
  · exact (hG.comp (hR.comp measurable_swap)).aemeasurable

/- English proof (translation)
Use `set P : V → Polynomial ℂ := fun u => ∑ d ∈ Finset.range (D + 1), Polynomial.C (c d u) * Polynomial.X ^ d with hPdef`. Establish `hPeval : ∀ θ u, (P u).eval (circleMap 0 1 θ) = F (R θ u)`. Introduce `θ u`. Rewrite using `[hexp, hPdef, Polynomial.eval_finsetSum]`. Simplify using the standard rewrite rules.

Establish `hPcoeff : ∀ u, (P u).coeff d0 = c d0 u`. Introduce `u`. Rewrite using `[hPdef, Polynomial.finsetSum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_eq_single d0]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hd0)) h`.

Establish `hPdeg : ∀ u, (P u).natDegree ≤ D`. Introduce `u`. Use `Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_` and prove the remaining obligations. Conclude with `(Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))`. Establish `hRS : ∀ θ u, u ∈ S → R θ u ∈ S`.

Introduce `θ u hu`. Establish `: u ∈ R θ ⁻¹' S` using `by rw [hinv θ]; exact hu`. Conclude with `this`. Establish `hFm : Measurable fun u => Real.log ‖F u‖` using `Real.measurable_log.comp hF.norm`. Use `⟨⟨hFm.aestronglyMeasurable, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `set K : ℝ := 4 * Real.pi * Real.log (max M 1) + 2 * Real.pi * D * Real.log 2 with hK`. Establish `hbound : ∀ᵐ u ∂(μ.restrict S), ∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖F (R θ u)‖‖ₑ ≤ ENNReal.ofReal (K + 2 * Real.pi * |Real.log ‖c d0 u‖|)` using `by filter_upwards [hnz, ae_restrict_mem hS] with u hu huS`. Use `lintegral_abs_log_circle_le (P u) D d0 M (hPdeg u) (by rw [hPcoeff]; exact hu) (fun θ => by rw [hPeval]; exact hM _ (hRS θ u huS))` as an intermediate fact. Establish `e : (fun θ => ‖Real.log ‖F (R θ u)‖‖ₑ) = fun θ => ‖Real.log ‖(P u).eval (circleMap 0 1 θ)‖‖ₑ`. Use function extensionality and compare the values at `θ`.

Rewrite using `[hPeval]`. Rewrite using `[e, ← hPcoeff u]`. Conclude with `this`. Establish `hrot` using `setLIntegral_rot μ S hS R hR hpres hinv (fun u => ‖Real.log ‖F u‖‖ₑ) (hFm.enorm)`. Establish `hKint : Integrable (fun u => K + 2 * Real.pi * |Real.log ‖c d0 u‖|) (μ.restrict S)`.

Establish `: IsFiniteMeasure (μ.restrict S)` using `isFiniteMeasure_restrict.mpr hSfin`. Conclude with `(integrable_const K).add (hint.abs.const_mul _)`. Establish `hlt : ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖F (R θ u)‖‖ₑ) ∂μ < ⊤` using `(lintegral_mono_ae hbound).trans_lt hKint.lintegral_lt_top`. Rewrite `hlt` using `[← hrot]`. Establish `h2 : ENNReal.ofReal (2 * Real.pi) ≠ 0` using `(ENNReal.ofReal_pos.mpr (by positivity)).ne'`.

Use `(ENNReal.mul_lt_top_iff.mp hlt)` as an intermediate fact. Break down `this with ⟨-, h⟩ | h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h h2`. Express the relevant statement in the definitionally equal form `∫⁻ u in S, ‖Real.log ‖F u‖‖ₑ ∂μ < ⊤`.

Rewrite using `[h]`. Conclude with `ENNReal.zero_lt_top`. Establish `hZ : MeasurableSet {u | F u = 0}` using `hF (measurableSet_singleton 0)`. Establish `hrot` using `setLIntegral_rot μ S hS R hR hpres hinv ({u | F u = 0}.indicator 1) (measurable_one.indicator hZ)`. Establish `hinner : ∀ᵐ u ∂(μ.restrict S), ∫⁻ θ in Ioc 0 (2 * Real.pi), {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u) = 0` using `by filter_upwards [hnz] with u hu`.

Establish `hPu : P u ≠ 0` using `fun h => hu (by rw [← hPcoeff, h]; simp)`. Establish `hc` using `countable_eval_circleMap_eq_zero (P u) hPu`. Establish `: (fun θ => {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u)) = {θ : ℝ | (P u).eval (circleMap 0 1 θ) = 0}.indicator 1`. Use function extensionality and compare the values at `θ`. Simplify using `only [Set.indicator, mem_ofPred_eq, hPeval, Pi.one_apply]`.

Rewrite using `[this, lintegral_indicator_one hc.measurableSet]`. Conclude with `hc.measure_zero _`. Establish `h0 : ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u)) ∂μ = 0`. Rewrite using `[lintegral_congr_ae hinner, lintegral_zero]`. Rewrite `hrot` using `[h0, lintegral_indicator_one hZ]`.

Establish `h2 : ENNReal.ofReal (2 * Real.pi) ≠ 0` using `(ENNReal.ofReal_pos.mpr (by positivity)).ne'`. Establish `h3` using `(mul_eq_zero.mp hrot).resolve_left h2`. Rewrite using `[ae_iff]`. Simplify using `using h3`.
-/
theorem circle_lemma {V : Type*} [MeasurableSpace V] (μ : Measure V) [SFinite μ]
    (S : Set V) (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤)
    (R : ℝ → V → V) (hR : Measurable (Function.uncurry R))
    (hpres : ∀ θ, MeasurePreserving (R θ) μ μ) (hinv : ∀ θ, R θ ⁻¹' S = S)
    (F : V → ℂ) (hF : Measurable F) (c : ℕ → V → ℂ) (D d0 : ℕ) (hd0 : d0 ≤ D)
    (hexp : ∀ θ u, F (R θ u) = ∑ d ∈ Finset.range (D + 1), c d u * circleMap 0 1 θ ^ d)
    (hint : IntegrableOn (fun u => Real.log ‖c d0 u‖) S μ)
    (hnz : ∀ᵐ u ∂(μ.restrict S), c d0 u ≠ 0)
    (M : ℝ) (hM : ∀ u ∈ S, ‖F u‖ ≤ M) :
    IntegrableOn (fun u => Real.log ‖F u‖) S μ ∧ ∀ᵐ u ∂(μ.restrict S), F u ≠ 0 := by
  classical

  set P : V → Polynomial ℂ := fun u =>
    ∑ d ∈ Finset.range (D + 1), Polynomial.C (c d u) * Polynomial.X ^ d with hPdef
  have hPeval : ∀ θ u, (P u).eval (circleMap 0 1 θ) = F (R θ u) := by
    intro θ u
    rw [hexp, hPdef, Polynomial.eval_finsetSum]
    simp
  have hPcoeff : ∀ u, (P u).coeff d0 = c d0 u := by
    intro u
    rw [hPdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single d0]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hd0)) h
  have hPdeg : ∀ u, (P u).natDegree ≤ D := by
    intro u
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))
  have hRS : ∀ θ u, u ∈ S → R θ u ∈ S := by
    intro θ u hu
    have : u ∈ R θ ⁻¹' S := by rw [hinv θ]; exact hu
    exact this
  have hFm : Measurable fun u => Real.log ‖F u‖ := Real.measurable_log.comp hF.norm
  refine ⟨⟨hFm.aestronglyMeasurable, ?_⟩, ?_⟩
  ·
    set K : ℝ := 4 * Real.pi * Real.log (max M 1) + 2 * Real.pi * D * Real.log 2 with hK
    have hbound : ∀ᵐ u ∂(μ.restrict S),
        ∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖F (R θ u)‖‖ₑ ≤
          ENNReal.ofReal (K + 2 * Real.pi * |Real.log ‖c d0 u‖|) := by
      filter_upwards [hnz, ae_restrict_mem hS] with u hu huS
      have := lintegral_abs_log_circle_le (P u) D d0 M (hPdeg u) (by rw [hPcoeff]; exact hu)
        (fun θ => by rw [hPeval]; exact hM _ (hRS θ u huS))
      have e : (fun θ => ‖Real.log ‖F (R θ u)‖‖ₑ) =
          fun θ => ‖Real.log ‖(P u).eval (circleMap 0 1 θ)‖‖ₑ := by
        funext θ; rw [hPeval]
      rw [e, ← hPcoeff u]
      exact this
    have hrot := setLIntegral_rot μ S hS R hR hpres hinv (fun u => ‖Real.log ‖F u‖‖ₑ)
      (hFm.enorm)
    have hKint : Integrable (fun u => K + 2 * Real.pi * |Real.log ‖c d0 u‖|) (μ.restrict S) := by
      have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSfin
      exact (integrable_const K).add (hint.abs.const_mul _)
    have hlt : ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖F (R θ u)‖‖ₑ) ∂μ < ⊤ :=
      (lintegral_mono_ae hbound).trans_lt hKint.lintegral_lt_top
    rw [← hrot] at hlt
    have h2 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have := (ENNReal.mul_lt_top_iff.mp hlt)
    rcases this with ⟨-, h⟩ | h | h
    · exact h
    · exact absurd h h2
    · change ∫⁻ u in S, ‖Real.log ‖F u‖‖ₑ ∂μ < ⊤
      rw [h]; exact ENNReal.zero_lt_top
  ·
    have hZ : MeasurableSet {u | F u = 0} := hF (measurableSet_singleton 0)
    have hrot := setLIntegral_rot μ S hS R hR hpres hinv ({u | F u = 0}.indicator 1)
      (measurable_one.indicator hZ)
    have hinner : ∀ᵐ u ∂(μ.restrict S),
        ∫⁻ θ in Ioc 0 (2 * Real.pi), {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u) = 0 := by
      filter_upwards [hnz] with u hu
      have hPu : P u ≠ 0 := fun h => hu (by rw [← hPcoeff, h]; simp)
      have hc := countable_eval_circleMap_eq_zero (P u) hPu
      have : (fun θ => {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u)) =
          {θ : ℝ | (P u).eval (circleMap 0 1 θ) = 0}.indicator 1 := by
        funext θ
        simp only [Set.indicator, mem_ofPred_eq, hPeval, Pi.one_apply]
      rw [this, lintegral_indicator_one hc.measurableSet]
      exact hc.measure_zero _
    have h0 : ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi),
        {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u)) ∂μ = 0 := by
      rw [lintegral_congr_ae hinner, lintegral_zero]
    rw [h0, lintegral_indicator_one hZ] at hrot
    have h2 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have h3 := (mul_eq_zero.mp hrot).resolve_left h2
    rw [ae_iff]
    simpa using h3

end LogInt

end

end GroundTheory.Heights₂.Heights
