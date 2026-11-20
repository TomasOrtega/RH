import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRect

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `h1 : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w) ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1) 1` using `(hasDerivAt_id' (1 : ℂ)).const_cpow (Or.inl (by exact_mod_cast hy.ne'))`. Establish `h2` using `h1.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero`. Establish `e : ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1 * 1 - (y : ℂ) ^ (1 : ℂ) * 1) / 1 ^ 2 = (y : ℂ) * (Real.log y : ℂ) - y`. Rewrite using `[Complex.cpow_one, ← Complex.ofReal_log hy.le]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h2.congr_deriv e`.
-/
theorem ex_phi_hasDerivAt (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := by
  have h1 : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w) ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1) 1 :=
    (hasDerivAt_id' (1 : ℂ)).const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  have h2 := h1.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
  have e : ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1 * 1 - (y : ℂ) ^ (1 : ℂ) * 1) / 1 ^ 2 =
      (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [Complex.cpow_one, ← Complex.ofReal_log hy.le]
    ring
  exact h2.congr_deriv e

/- English proof (translation)
Introduce `w hw`. Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hw`. Conclude with `((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).div differentiableAt_id hw0).differentiableWithinAt`.
-/
theorem ex_phi_differentiableOn (y : ℝ) (hy : 0 < y) :
    DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := by
  intro w hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  exact ((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).div differentiableAt_id hw0).differentiableWithinAt

/- English proof (translation)
Establish `hb : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1` using `ex_phi_hasDerivAt y hy`. Establish `hU : IsOpen {w : ℂ | 0 < w.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `h1U : {w : ℂ | 0 < w.re} ∈ nhds (1 : ℂ)` using `hU.mem_nhds (by simp)`. Establish `hφd : DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re}` using `ex_phi_differentiableOn y hy`. Establish `hG : DifferentiableOn ℂ (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) {w : ℂ | 0 < w.re}` using `(differentiableOn_dslope h1U).2 ((differentiableOn_dslope h1U).2 hφd)`.

Establish `hd1 : dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1 1 = (y : ℂ) * (Real.log y : ℂ) - y`. Rewrite using `[dslope_same, hb.deriv]`. Use `Formalism.ZF.rectangle_double_pole (fun w => exKer y w / (w - 1)) (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) (y : ℂ) ((y : ℂ) * (Real.log y : ℂ) - y) 1 x₀ x₁ y₀ y₁ (by simpa using hx₀1) (by simpa using hx₁) (by simpa using hy₀) (by simpa using hy₁) ⟨{w : ℂ | 0 < w.re}, …` and prove the remaining obligations. Introduce `z hz`. Rewrite `hz` using `[Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]`.

Use `show 0 < z.re`. Combine the linear relations using `[hz.1.1]`. Introduce `w hw`. Establish `hw1 : w - 1 ≠ 0` using `sub_ne_zero.mpr hw`. Rewrite using `[dslope_of_ne _ hw, slope_def_field, dslope_of_ne _ hw, slope_def_field, hd1]`.

Simplify using `only [exKer, Complex.cpow_one, div_one]`. Distinguish the cases in `h0 : w = 0`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_rect_double (y : ℝ) (hy : 0 < y) (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) :
    Formalism.ZF.rectInt (fun w => exKer y w / (w - 1)) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * ((y : ℂ) * (Real.log y : ℂ) - y) := by
  have hb : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := ex_phi_hasDerivAt y hy
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1U : {w : ℂ | 0 < w.re} ∈ nhds (1 : ℂ) := hU.mem_nhds (by simp)
  have hφd : DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := ex_phi_differentiableOn y hy
  have hG : DifferentiableOn ℂ (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) {w : ℂ | 0 < w.re} :=
    (differentiableOn_dslope h1U).2 ((differentiableOn_dslope h1U).2 hφd)
  have hd1 : dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1 1 = (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [dslope_same, hb.deriv]
  refine Formalism.ZF.rectangle_double_pole (fun w => exKer y w / (w - 1))
    (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) (y : ℂ) ((y : ℂ) * (Real.log y : ℂ) - y) 1 x₀ x₁ y₀ y₁
    (by simpa using hx₀1) (by simpa using hx₁) (by simpa using hy₀) (by simpa using hy₁)
    ⟨{w : ℂ | 0 < w.re}, hU, ?_, hG⟩ ?_
  · intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hz
    show 0 < z.re
    linarith [hz.1.1]
  · intro w hw
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    rw [dslope_of_ne _ hw, slope_def_field, dslope_of_ne _ hw, slope_def_field, hd1]
    simp only [exKer, Complex.cpow_one, div_one]
    by_cases h0 : w = 0
    · subst h0
      simp
      ring
    · field_simp
      ring

def exBdry (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {w : ℂ | x₀ ≤ w.re ∧ w.re ≤ x₁ ∧ y₀ ≤ w.im ∧ w.im ≤ y₁ ∧
    (w.re = x₀ ∨ w.re = x₁ ∨ w.im = y₀ ∨ w.im = y₁)}

/- English proof (translation)
Rewrite `h` using `[Set.uIcc_of_le hx]`. Take `⟨h1, h2⟩` from `h`. Establish `hc' : y₀ ≤ c ∧ c ≤ y₁`. Apply the tactic sequence `rcases hc with rfl | rfl <;> constructor <;> linarith`. Use `⟨by simpa using h1, by simpa using h2, by simpa using hc'.1, by simpa using hc'.2, ?_⟩` and prove the remaining obligations.

Use `right`. Use `right`. Simplify using `using hc`.
-/
theorem ex_mem_horiz {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = y₀ ∨ c = y₁) {x : ℝ}
    (h : x ∈ Set.uIcc x₀ x₁) : ((x : ℂ) + c * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hx] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : y₀ ≤ c ∧ c ≤ y₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using h1, by simpa using h2, by simpa using hc'.1, by simpa using hc'.2, ?_⟩
  right; right
  simpa using hc

/- English proof (translation)
Rewrite `h` using `[Set.uIcc_of_le hy]`. Take `⟨h1, h2⟩` from `h`. Establish `hc' : x₀ ≤ c ∧ c ≤ x₁`. Apply the tactic sequence `rcases hc with rfl | rfl <;> constructor <;> linarith`. Use `⟨by simpa using hc'.1, by simpa using hc'.2, by simpa using h1, by simpa using h2, ?_⟩` and prove the remaining obligations.

Break down `hc with hc | hc` into its components or cases. Use `left`. Simplify using `using hc`. Use `right`. Use `left`.

Simplify using `using hc`.
-/
theorem ex_mem_vert {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = x₀ ∨ c = x₁) {t : ℝ}
    (h : t ∈ Set.uIcc y₀ y₁) : ((c : ℂ) + t * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hy] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : x₀ ≤ c ∧ c ≤ x₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using hc'.1, by simpa using hc'.2, by simpa using h1, by simpa using h2, ?_⟩
  rcases hc with hc | hc
  · left
    simpa using hc
  · right; left
    simpa using hc

/- English proof (translation)
Establish `hh : ∀ c : ℝ, (c = y₀ ∨ c = y₁) → (∫ x : ℝ in x₀..x₁, f (x + c * I)) = ∫ x : ℝ in x₀..x₁, g (x + c * I)`. Introduce `c hc`. Conclude with `intervalIntegral.integral_congr fun x hx' => h _ (ex_mem_horiz hx hy hc hx')`. Establish `hv : ∀ c : ℝ, (c = x₀ ∨ c = x₁) → (∫ t : ℝ in y₀..y₁, f (c + t * I)) = ∫ t : ℝ in y₀..y₁, g (c + t * I)`. Introduce `c hc`.

Conclude with `intervalIntegral.integral_congr fun t ht => h _ (ex_mem_vert hx hy hc ht)`. Unfold `Formalism.ZF.rectInt`. Rewrite using `[hh y₀ (Or.inl rfl), hh y₁ (Or.inr rfl), hv x₀ (Or.inl rfl), hv x₁ (Or.inr rfl)]`.
-/
theorem ex_rectInt_congr {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ w ∈ exBdry x₀ x₁ y₀ y₁, f w = g w) :
    Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ = Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  have hh : ∀ c : ℝ, (c = y₀ ∨ c = y₁) →
      (∫ x : ℝ in x₀..x₁, f (x + c * I)) = ∫ x : ℝ in x₀..x₁, g (x + c * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun x hx' => h _ (ex_mem_horiz hx hy hc hx')
  have hv : ∀ c : ℝ, (c = x₀ ∨ c = x₁) →
      (∫ t : ℝ in y₀..y₁, f (c + t * I)) = ∫ t : ℝ in y₀..y₁, g (c + t * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun t ht => h _ (ex_mem_vert hx hy hc ht)
  unfold Formalism.ZF.rectInt
  rw [hh y₀ (Or.inl rfl), hh y₁ (Or.inr rfl), hv x₀ (Or.inl rfl), hv x₁ (Or.inr rfl)]

/- English proof (translation)
Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Conclude with `hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + c * I).continuousOn fun x hx' => ex_mem_horiz hx hy hc hx'`.
-/
theorem ex_ii_horiz {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = y₀ ∨ c = y₁) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) MeasureTheory.volume x₀ x₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + c * I).continuousOn
    fun x hx' => ex_mem_horiz hx hy hc hx'

/- English proof (translation)
Apply `ContinuousOn.intervalIntegrable` to reduce the goal to its premises. Conclude with `hf.comp (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * I).continuousOn fun t ht => ex_mem_vert hx hy hc ht`.
-/
theorem ex_ii_vert {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = x₀ ∨ c = x₁) :
    IntervalIntegrable (fun t : ℝ => f (c + t * I)) MeasureTheory.volume y₀ y₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * I).continuousOn
    fun t ht => ex_mem_vert hx hy hc ht

/- English proof (translation)
Unfold `Formalism.ZF.rectInt`. Rewrite using `[intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inl rfl)) (ex_ii_horiz hx hy hg (Or.inl rfl)), intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inr rfl)) (ex_ii_horiz hx hy hg (Or.inr rfl)), intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inr rfl)) (ex_ii_v …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_rectInt_add {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) (hg : ContinuousOn g (exBdry x₀ x₁ y₀ y₁)) :
    Formalism.ZF.rectInt (fun w => f w + g w) x₀ x₁ y₀ y₁ =
      Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ + Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  unfold Formalism.ZF.rectInt
  rw [intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inl rfl)) (ex_ii_horiz hx hy hg (Or.inl rfl)),
    intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inr rfl)) (ex_ii_horiz hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inr rfl)) (ex_ii_vert hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inl rfl)) (ex_ii_vert hx hy hg (Or.inl rfl))]
  ring

/- English proof (translation)
Establish `hy0 : (y : ℂ) ≠ 0` using `by exact_mod_cast hy.ne'`. Unfold `exKer`. Apply `ContinuousAt.div` to reduce the goal to its premises. Conclude with `continuousAt_const_cpow hy0`. Use `fun_prop`.

Conclude with `mul_ne_zero h0 (sub_ne_zero.mpr h1)`.
-/
theorem exKer_continuousAt (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    ContinuousAt (exKer y) w := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  unfold exKer
  apply ContinuousAt.div
  · exact continuousAt_const_cpow hy0
  · fun_prop
  · exact mul_ne_zero h0 (sub_ne_zero.mpr h1)

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `hw`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce and unpack `rfl`. Simplify using `at h5`. Apply the tactic sequence `rcases h5 with h | h | h | h <;> linarith`.
-/
theorem ex_bdry_ne {x₀ x₁ y₀ y₁ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) {w : ℂ} (hw : w ∈ exBdry x₀ x₁ y₀ y₁) : w ≠ 0 ∧ w ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  constructor
  · rintro rfl
    simp at h1
    linarith
  · rintro rfl
    simp at h5
    rcases h5 with h | h | h | h <;> linarith

/- English proof (translation)
Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem neg_div_mul_eq_neg_add_div_mul_add_div (a b K u : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) :
    -(b / a) * K = -((1 * a + u * b) / (u * a)) * K + K / u := by
  field_simp
  ring

set_option maxHeartbeats 800000 in
/- English proof (translation)
Establish `hfd : Differentiable ℂ (exLF χ)` using `exLF_differentiable χ`. Establish `hx : σ₁ ≤ σ₀` using `by linarith`. Establish `hyy : -T' ≤ T'` using `by linarith`. Establish `hZ' : ∀ ρ : ℂ, ρ ∈ Z ↔ exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ ρ.re < σ₀ ∧ -T' < ρ.im ∧ ρ.im < T'`. Introduce `ρ`.

Rewrite using `[hZ ρ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h1, h2⟩`. Use `exLF_re_lt_one χ h0` as an intermediate fact. Conclude with `⟨h0, h1, by linarith, (abs_lt.mp h2).1, (abs_lt.mp h2).2⟩`.

Introduce and unpack `⟨h0, h1, -, h3, h4⟩`. Conclude with `⟨h0, h1, abs_lt.mpr ⟨h3, h4⟩⟩`. Establish `hedge' : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → -T' ≤ w.im → w.im ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ w.re < σ₀ ∧ -T' < w.im ∧ w.im < T'`. Introduce `w h1 h2 h3 h4 h0`. Take `⟨h5, h6⟩` from `hedge w h1 h2 (abs_le.mpr ⟨h3, h4⟩) h0`.

Use `exLF_re_lt_one χ h0` as an intermediate fact. Conclude with `⟨h5, by linarith, (abs_lt.mp h6).1, (abs_lt.mp h6).2⟩`. Establish `hmain` using `ex_rect_logDeriv (exLF χ) hfd (exLF_one_ne_zero χ) y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀ (by linarith) hT' Z hZ' hedge'`. Distinguish the cases in `hχ : χ = 1`. Substitute `hχ` using the available equality.

Establish `hbd : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', w ≠ 0 ∧ w ≠ 1 ∧ exLF (1 : DirichletCharacter ℂ M) w ≠ 0`. Introduce `w hw`. Take `⟨h0, h1⟩` from `ex_bdry_ne hσ₁ hσ₁1 hσ₀ (by linarith) hT' hw`. Use `⟨h0, h1, fun hfw => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2, a3, a4, a5⟩` from `hw`.

Take `⟨b1, b2, b3, b4⟩` from `hedge' w a1 a2 a3 a4 hfw`. Apply the tactic sequence `rcases a5 with h | h | h | h <;> linarith`. Establish `hA : ContinuousOn (fun w => -(deriv (exLF (1 : DirichletCharacter ℂ M)) w / exLF (1 : DirichletCharacter ℂ M) w) * exKer y w) (exBdry σ₁ σ₀ (-T') T')`. Introduce `w hw`. Take `⟨h0, h1, h2⟩` from `hbd w hw`.

Establish `hd : ContinuousAt (deriv (exLF (1 : DirichletCharacter ℂ M))) w` using `(hfd.analyticAt w).deriv.continuousAt`. Conclude with `(((hd.div (hfd w).continuousAt h2).neg).mul (exKer_continuousAt y hy h0 h1)).continuousWithinAt`. Establish `hK : ContinuousOn (fun w => exKer y w / (w - 1)) (exBdry σ₁ σ₀ (-T') T')`. Introduce `w hw`. Take `⟨h0, h1, -⟩` from `hbd w hw`.

Establish `hs : ContinuousAt (fun s : ℂ => s - 1) w` using `continuousAt_id.sub continuousAt_const`. Conclude with `((exKer_continuousAt y hy h0 h1).div hs (sub_ne_zero.mpr h1)).continuousWithinAt`. Establish `hB : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', Fchi (1 : DirichletCharacter ℂ M) y w = -(deriv (exLF (1 : DirichletCharacter ℂ M)) w / exLF (1 : DirichletCharacter ℂ M) w) * exKer y w + exKer y w / (w - 1)`. Introduce `w hw`. Take `⟨h0, h1, h2⟩` from `hbd w hw`.

Establish `hw1 : w - 1 ≠ 0` using `sub_ne_zero.mpr h1`. Establish `hfw : exLF (1 : DirichletCharacter ℂ M) w = (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w` using `exLF_one_char_apply h1`. Establish `hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w ≠ 0`. Introduce `h`. Apply `h2` to reduce the goal to its premises.

Rewrite using `[hfw, h, mul_zero]`. Establish `hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w` using `DirichletCharacter.differentiableAt_LFunction 1 w (Or.inl h1)`. Establish `hev : exLF (1 : DirichletCharacter ℂ M) =ᶠ[nhds w] fun s => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s` using `(eventually_ne_nhds h1).mono fun s hs => exLF_one_char_apply hs`. Establish `hder : deriv (exLF (1 : DirichletCharacter ℂ M)) w = 1 * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w + (w - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w`. Rewrite using `[hev.deriv_eq]`.

Conclude with `(((hasDerivAt_id' w).sub_const 1).mul hLd.hasDerivAt).deriv`. Establish `e1 : Fchi (1 : DirichletCharacter ℂ M) y w = -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w) * exKer y w`. Simplify using `only [Fchi, negLD, exKer, mul_div_assoc]`. Rewrite using `[e1, hder, hfw]`. Conclude with `neg_div_mul_eq_neg_add_div_mul_add_div _ _ _ _ hL hw1`.

Rewrite using `[ex_rectInt_congr hx hyy hB, ex_rectInt_add hx hyy hA hK, hmain, ex_rect_double y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀ (by linarith) hT', if_pos rfl]`. Simplify using `only [explicitFormulaConstant, exOrd]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfL : exLF χ = DirichletCharacter.LFunction χ` using `exLF_of_ne hχ`. Establish `hF : Fchi χ y = fun w => -(deriv (exLF χ) w / exLF χ w) * exKer y w`.

Use function extensionality and compare the values at `w`. Simplify using `only [Fchi, negLD, exKer, hfL, mul_div_assoc]`. Rewrite using `[hF, hmain, if_neg hχ]`. Simplify using `only [explicitFormulaConstant, exOrd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ex_rect_Fchi {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y : ℝ) (hy : 0 < y) (σ₁ σ₀ T' : ℝ)
    (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT' : 0 < T')
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T'))
    (hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T') :
    Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T') T' =
      2 * Real.pi * I * (explicitFormulaConstant χ * y + (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) -
        ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) := by
  have hfd : Differentiable ℂ (exLF χ) := exLF_differentiable χ
  have hx : σ₁ ≤ σ₀ := by linarith
  have hyy : -T' ≤ T' := by linarith
  have hZ' : ∀ ρ : ℂ, ρ ∈ Z ↔ exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ ρ.re < σ₀ ∧ -T' < ρ.im ∧ ρ.im < T' := by
    intro ρ
    rw [hZ ρ]
    constructor
    · rintro ⟨h0, h1, h2⟩
      have := exLF_re_lt_one χ h0
      exact ⟨h0, h1, by linarith, (abs_lt.mp h2).1, (abs_lt.mp h2).2⟩
    · rintro ⟨h0, h1, -, h3, h4⟩
      exact ⟨h0, h1, abs_lt.mpr ⟨h3, h4⟩⟩
  have hedge' : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → -T' ≤ w.im → w.im ≤ T' → exLF χ w = 0 →
      σ₁ < w.re ∧ w.re < σ₀ ∧ -T' < w.im ∧ w.im < T' := by
    intro w h1 h2 h3 h4 h0
    obtain ⟨h5, h6⟩ := hedge w h1 h2 (abs_le.mpr ⟨h3, h4⟩) h0
    have := exLF_re_lt_one χ h0
    exact ⟨h5, by linarith, (abs_lt.mp h6).1, (abs_lt.mp h6).2⟩
  have hmain := ex_rect_logDeriv (exLF χ) hfd (exLF_one_ne_zero χ) y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀
    (by linarith) hT' Z hZ' hedge'
  by_cases hχ : χ = 1
  · subst hχ
    have hbd : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', w ≠ 0 ∧ w ≠ 1 ∧ exLF (1 : DirichletCharacter ℂ M) w ≠ 0 := by
      intro w hw
      obtain ⟨h0, h1⟩ := ex_bdry_ne hσ₁ hσ₁1 hσ₀ (by linarith) hT' hw
      refine ⟨h0, h1, fun hfw => ?_⟩
      obtain ⟨a1, a2, a3, a4, a5⟩ := hw
      obtain ⟨b1, b2, b3, b4⟩ := hedge' w a1 a2 a3 a4 hfw
      rcases a5 with h | h | h | h <;> linarith
    have hA : ContinuousOn (fun w => -(deriv (exLF (1 : DirichletCharacter ℂ M)) w /
        exLF (1 : DirichletCharacter ℂ M) w) * exKer y w) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hd : ContinuousAt (deriv (exLF (1 : DirichletCharacter ℂ M))) w :=
        (hfd.analyticAt w).deriv.continuousAt
      exact (((hd.div (hfd w).continuousAt h2).neg).mul (exKer_continuousAt y hy h0 h1)).continuousWithinAt
    have hK : ContinuousOn (fun w => exKer y w / (w - 1)) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, -⟩ := hbd w hw
      have hs : ContinuousAt (fun s : ℂ => s - 1) w := continuousAt_id.sub continuousAt_const
      exact ((exKer_continuousAt y hy h0 h1).div hs (sub_ne_zero.mpr h1)).continuousWithinAt
    have hB : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', Fchi (1 : DirichletCharacter ℂ M) y w =
        -(deriv (exLF (1 : DirichletCharacter ℂ M)) w / exLF (1 : DirichletCharacter ℂ M) w) * exKer y w +
          exKer y w / (w - 1) := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hfw : exLF (1 : DirichletCharacter ℂ M) w =
          (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := exLF_one_char_apply h1
      have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w ≠ 0 := by
        intro h
        apply h2
        rw [hfw, h, mul_zero]
      have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w :=
        DirichletCharacter.differentiableAt_LFunction 1 w (Or.inl h1)
      have hev : exLF (1 : DirichletCharacter ℂ M) =ᶠ[nhds w]
          fun s => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s :=
        (eventually_ne_nhds h1).mono fun s hs => exLF_one_char_apply hs
      have hder : deriv (exLF (1 : DirichletCharacter ℂ M)) w =
          1 * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w +
            (w - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w := by
        rw [hev.deriv_eq]
        exact (((hasDerivAt_id' w).sub_const 1).mul hLd.hasDerivAt).deriv
      have e1 : Fchi (1 : DirichletCharacter ℂ M) y w =
          -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w /
            DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w) * exKer y w := by
        simp only [Fchi, negLD, exKer, mul_div_assoc]
      rw [e1, hder, hfw]
      exact neg_div_mul_eq_neg_add_div_mul_add_div _ _ _ _ hL hw1
    rw [ex_rectInt_congr hx hyy hB, ex_rectInt_add hx hyy hA hK, hmain,
      ex_rect_double y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀ (by linarith) hT', if_pos rfl]
    simp only [explicitFormulaConstant, exOrd]
    ring
  · have hfL : exLF χ = DirichletCharacter.LFunction χ := exLF_of_ne hχ
    have hF : Fchi χ y = fun w => -(deriv (exLF χ) w / exLF χ w) * exKer y w := by
      funext w
      simp only [Fchi, negLD, exKer, hfL, mul_div_assoc]
    rw [hF, hmain, if_neg hχ]
    simp only [explicitFormulaConstant, exOrd]
    ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
