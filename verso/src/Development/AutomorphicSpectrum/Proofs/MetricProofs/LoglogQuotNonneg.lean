import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.PullDominateStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
Establish `h1 : Real.exp 1 ≤ Real.log (1 / t)`. Rewrite using `[one_div, Real.log_inv]`. Use `Real.log_le_log ht hte` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `Real.log_le_log (Real.exp_pos 1) h1` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis.
-/
theorem log_inv_bounds {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    Real.exp 1 ≤ Real.log (1 / t) ∧ 1 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : Real.exp 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  refine ⟨h1, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at this

/- English proof (translation)
Take `⟨h1, h2⟩` from `log_inv_bounds ht hte`. Conclude with `div_nonneg (by linarith) (by linarith [Real.exp_pos 1])`.
-/
theorem loglog_quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_bounds ht hte
  exact div_nonneg (by linarith) (by linarith [Real.exp_pos 1])

/- English proof (translation)
Rewrite using `[epsT, mul_div_assoc]`.
-/
theorem epsT_eq_mul (C t : ℝ) :
    epsT C t = C * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) := by
  rw [epsT, mul_div_assoc]

/- English proof (translation)
Rewrite using `[epsT_eq_mul, epsT_eq_mul]`. Conclude with `mul_le_mul_of_nonneg_right hC (loglog_quot_nonneg ht hte)`.
-/
theorem epsT_le_epsT {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C' t := by
  rw [epsT_eq_mul, epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (loglog_quot_nonneg ht hte)

/- English proof (translation)
Establish `hx` using `loglog_quot_nonneg ht hte`. Rewrite using `[epsT_eq_mul, epsT_eq_mul, ← mul_assoc, ← mul_assoc]`. Use `mul_le_mul_of_nonneg_right ?_ hx` and prove the remaining obligations. Establish `h2 : C ^ 2 ≤ C' ^ 2`. Rewrite using `[← sq_abs C]`.

Conclude with `pow_le_pow_left₀ (abs_nonneg C) hC 2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem mul_epsT_le {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : C * epsT C t ≤ C' * epsT C' t := by
  have hx := loglog_quot_nonneg ht hte
  rw [epsT_eq_mul, epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

/- English proof (translation)
Introduce `x j y hy w`. Take `⟨hyt, hyU⟩` from `hy`. Establish `hU : (A.chart j).symm y ∈ (th.U x ∩ Set.univ) ∩ Θ.U x` using `hyU`. Establish `hO1 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' th.U x)` using `(A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (th.isOpen_U x)`. Establish `hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x)` using `(A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)`.

Establish `hO3 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Set.univ : Set X))` using `(A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target isOpen_univ`. Establish `hth2 : ContDiffAt ℝ 2 (th.φ x ∘ (A.chart j).symm) y` using `((hth.1 x j).contDiffAt (hO1.mem_nhds ⟨hyt, hU.1.1⟩)).of_le (by norm_cast)`. Establish `hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y` using `((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)`. Establish `hu2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y` using `((hu j).contDiffAt (hO3.mem_nhds ⟨hyt, Set.mem_univ _⟩)).of_le (by norm_cast)`. Establish `hP2 : ContDiffAt ℝ 2 ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y` using `(hth2.add hu2).add (contDiffAt_const.mul hΘ2)`.

Establish `hfun : (th + LocPot.ofFun u + Θ.rsmul ε').φ x ∘ (A.chart j).symm = fun z => ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) z + (ε' - ε) * (Θ.φ x ∘ (A.chart j).symm) z`. Use function extensionality and compare the values at `z`. Use `show th.φ x _ + u _ + ε' * Θ.φ x _ = th.φ x _ + u _ + ε * Θ.φ x _ + (ε' - ε) * Θ.φ x _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, levi_add_smul (ε' - ε) hP2 hΘ2 w]`.

Conclude with `add_nonneg (h x j y ⟨hyt, hyU⟩ w) (mul_nonneg (sub_nonneg.2 hε) (hΘp x j y ⟨hyt, hU.2⟩ w))`.
-/
theorem isPsh_rsmul_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) {ε ε' : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (hε : ε ≤ ε')
    (h : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε') := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hU : (A.chart j).symm y ∈ (th.U x ∩ Set.univ) ∩ Θ.U x := hyU
  have hO1 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' th.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (th.isOpen_U x)
  have hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)
  have hO3 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Set.univ : Set X)) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target isOpen_univ
  have hth2 : ContDiffAt ℝ 2 (th.φ x ∘ (A.chart j).symm) y :=
    ((hth.1 x j).contDiffAt (hO1.mem_nhds ⟨hyt, hU.1.1⟩)).of_le (by norm_cast)
  have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
    ((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)
  have hu2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
    ((hu j).contDiffAt (hO3.mem_nhds ⟨hyt, Set.mem_univ _⟩)).of_le (by norm_cast)
  have hP2 : ContDiffAt ℝ 2
      ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hth2.add hu2).add (contDiffAt_const.mul hΘ2)
  have hfun : (th + LocPot.ofFun u + Θ.rsmul ε').φ x ∘ (A.chart j).symm =
      fun z => ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) z +
        (ε' - ε) * (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show th.φ x _ + u _ + ε' * Θ.φ x _ = th.φ x _ + u _ + ε * Θ.φ x _ + (ε' - ε) * Θ.φ x _
    ring
  rw [hfun, levi_add_smul (ε' - ε) hP2 hΘ2 w]
  exact add_nonneg (h x j y ⟨hyt, hyU⟩ w)
    (mul_nonneg (sub_nonneg.2 hε) (hΘp x j y ⟨hyt, hU.2⟩ w))

/- English proof (translation)
Take `⟨-, ht₀1, hF⟩` from `hF`. Establish `hCC : C ≤ C'` using `(le_abs_self C).trans hC`. Establish `hr : ∀ y, 0 ≤ rW L s y` using `fun y => by`. Use `hs y` as an intermediate fact. Use `Real.exp_pos 1` as an intermediate fact.

Unfold `rW`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3, h4, h5, h6, h7, h8⟩` from `hF t ht (htt.trans ht₁₀)`. Establish `hte' : t ≤ Real.exp (-Real.exp 1)` using `htt.trans hte`.

Establish `hε` using `epsT_le_epsT hCC ht hte'`. Establish `hll` using `(log_inv_bounds ht hte').2`. Use `⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_, isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_, fun y hy => ?_, fun t' htt' ht' y => ?_⟩` and prove the remaining obligations. Use `h4 y` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Use `h6 y hy hyr` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `h7 y hy` as an intermediate fact. Use `mul_le_mul_of_nonneg_right hε (hr y)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `h8 t' htt' (ht'.trans ht₁₀) y` as an intermediate fact. Use `mul_epsT_le hC (ht.trans_le htt') (ht'.trans hte)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isRegFamily_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ C' t₁ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th)
    (hs : ∀ y, logNormSec L s y ≤ 0) (hF : IsRegFamily A Θ L s th ph phT C t₀)
    (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀) (hte : t₁ ≤ Real.exp (-Real.exp 1)) :
    IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y => by
    have := hs y
    have := Real.exp_pos 1
    unfold rW
    linarith
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-Real.exp 1) := htt.trans hte
  have hε := epsT_le_epsT hCC ht hte'
  have hll := (log_inv_bounds ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_, fun y hy => ?_,
    fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_le hC (ht.trans_le htt') (ht'.trans hte)
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
