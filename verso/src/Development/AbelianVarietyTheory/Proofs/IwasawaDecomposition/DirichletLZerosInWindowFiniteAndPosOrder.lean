import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

namespace GlobalTheory.Mem.An.ZeroWindow

open Complex DirichletCharacter

/- English proof (translation)
Use `DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton` and prove the remaining obligations. Introduce `s hs`. Conclude with `(χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt`.
-/
theorem analyticOff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
  intro s hs
  exact (χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt

/- English proof (translation)
Distinguish the cases in `h : χ = 1`. Substitute `h` using the available equality. Use `⟨LFunctionTrivChar₁ q, differentiable_LFunctionTrivChar₁ q, LFunctionTrivChar₁_apply_one_ne_zero q, fun s hs h0 => ?_⟩` and prove the remaining obligations. Rewrite using `[LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, h0, mul_zero]`. Conclude with `⟨LFunction χ, differentiable_LFunction h, LFunction_apply_one_ne_zero h, fun _ _ h0 => h0⟩`.
-/
theorem exists_entire {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 1 ≠ 0 ∧ ∀ s, s ≠ 1 → LFunction χ s = 0 → F s = 0 := by
  by_cases h : χ = 1
  · subst h
    refine ⟨LFunctionTrivChar₁ q, differentiable_LFunctionTrivChar₁ q,
      LFunctionTrivChar₁_apply_one_ne_zero q, fun s hs h0 => ?_⟩
    rw [LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, h0, mul_zero]
  · exact ⟨LFunction χ, differentiable_LFunction h, LFunction_apply_one_ne_zero h,
      fun _ _ h0 => h0⟩

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h2` using `h.2.1`. Simplify using `at h2`.
-/
theorem ne_one_of_mem {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {t T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosIn χ t T) : ρ ≠ 1 := by
  rintro rfl
  have h2 := h.2.1
  simp at h2

/- English proof (translation)
Take `⟨F, hF, h1, h0⟩` from `exists_entire χ`. Establish `hA : AnalyticOnNhd ℂ F Set.univ` using `hF.differentiableOn.analyticOnNhd isOpen_univ`. Assume the negation of the conclusion as `hinf`. Establish `hinf : (zerosIn χ t T).Infinite` using `hinf`. Establish `hsub : zerosIn χ t T ⊆ Metric.closedBall (0 : ℂ) (1 + |t| + T)`.

Introduce and unpack `ρ ⟨h0, h1, h2, -⟩`. Rewrite using `[mem_closedBall_zero_iff]`. Use `Complex.norm_le_abs_re_add_abs_im ρ` as an intermediate fact. Apply the tactic sequence `have h3 : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith`. Establish `h4 : |ρ.im| ≤ |t| + T`.

Use `abs_sub_abs_le_abs_sub ρ.im t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨z, -, hz⟩` from `hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall _ _) hsub`. Establish `hfr : ∃ᶠ w in nhdsWithin z {z}ᶜ, F w = 0`.

Rewrite `hz` using `[accPt_iff_frequently_nhdsNE]`. Conclude with `hz.mono fun w hw => h0 w (ne_one_of_mem hw) hw.2.2.2`. Use `hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ z) hfr` as an intermediate fact. Conclude with `h1 (this (Set.mem_univ 1))`.
-/
theorem finite_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) :
    (zerosIn χ t T).Finite := by
  obtain ⟨F, hF, h1, h0⟩ := exists_entire χ
  have hA : AnalyticOnNhd ℂ F Set.univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  by_contra hinf
  have hinf : (zerosIn χ t T).Infinite := hinf
  have hsub : zerosIn χ t T ⊆ Metric.closedBall (0 : ℂ) (1 + |t| + T) := by
    rintro ρ ⟨h0, h1, h2, -⟩
    rw [mem_closedBall_zero_iff]
    have := Complex.norm_le_abs_re_add_abs_im ρ
    have h3 : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h4 : |ρ.im| ≤ |t| + T := by
      have := abs_sub_abs_le_abs_sub ρ.im t
      linarith
    linarith
  obtain ⟨z, -, hz⟩ := hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall _ _) hsub
  have hfr : ∃ᶠ w in nhdsWithin z {z}ᶜ, F w = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hz
    exact hz.mono fun w hw => h0 w (ne_one_of_mem hw) hw.2.2.2
  have := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hfr
  exact h1 (this (Set.mem_univ 1))

/- English proof (translation)
Introduce `ht`. Rewrite `ht` using `[analyticOrderAt_eq_top]`. Establish `hc : IsPreconnected ({1}ᶜ : Set ℂ)` using `(isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected`. Establish `h2 : (2 : ℂ) ≠ 1` using `by norm_num`. Use `(analyticOff χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hρ ht` as an intermediate fact.

Conclude with `χ.LFunction_ne_zero_of_one_le_re (s := 2) (Or.inr h2) (by simp) (this h2)`.
-/
theorem order_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
  intro ht
  rw [analyticOrderAt_eq_top] at ht
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have := (analyticOff χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hρ ht
  exact χ.LFunction_ne_zero_of_one_le_re (s := 2) (Or.inr h2) (by simp) (this h2)

/- English proof (translation)
Unfold `zmult analyticOrderNatAt`. Establish `h1` using `order_ne_top χ (ne_one_of_mem hρ)`. Establish `h2 : analyticOrderAt (LFunction χ) ρ ≠ 0`. Rewrite using `[analyticOrderAt_ne_zero]`. Conclude with `⟨analyticOff χ ρ (ne_one_of_mem hρ), hρ.2.2.2⟩`.

Rewrite using `[Nat.one_le_iff_ne_zero]`. Simplify using `[h1, h2]`.
-/
theorem one_le_zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zerosIn χ t T) : 1 ≤ zmult χ ρ := by
  unfold zmult analyticOrderNatAt
  have h1 := order_ne_top χ (ne_one_of_mem hρ)
  have h2 : analyticOrderAt (LFunction χ) ρ ≠ 0 := by
    rw [analyticOrderAt_ne_zero]
    exact ⟨analyticOff χ ρ (ne_one_of_mem hρ), hρ.2.2.2⟩
  rw [Nat.one_le_iff_ne_zero]
  simp [h1, h2]

/- English proof (translation)
Introduce `_ _ χ t T` and use `⟨finite_zeros χ t T, fun _ hρ => one_le_zmult χ hρ⟩`.
-/
theorem finite_and_one_le_zmult : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ),
    (zerosIn χ t T).Finite ∧ ∀ ρ ∈ zerosIn χ t T, 1 ≤ zmult χ ρ :=
  fun _ _ χ t T => ⟨finite_zeros χ t T, fun _ hρ => one_le_zmult χ hρ⟩

end GlobalTheory.Mem.An.ZeroWindow
