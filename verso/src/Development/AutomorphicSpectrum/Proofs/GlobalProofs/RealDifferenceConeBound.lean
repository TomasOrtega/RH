import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue

/- English proof (translation)
Introduce `S G hG hS`. Establish `hopen : ∀ r : ℝ, IsOpen {s : ℂ | r < s.re}` using `fun r => isOpen_lt continuous_const Complex.continuous_re`. Establish `hagree : ∀ j k : ℕ, j ≤ k → Set.EqOn (G j) (G k) {s : ℂ | -(j : ℝ) < s.re}`. Introduce `j k hjk`. Establish `hsub : {s : ℂ | -(j : ℝ) < s.re} ⊆ {s : ℂ | -(k : ℝ) < s.re}`.

Introduce `s hs`. Establish `h1 : (j : ℝ) ≤ k` using `by exact_mod_cast hjk`. Simplify using `only [Set.mem_setOf_eq] at hs ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfj : AnalyticOnNhd ℂ (G j) {s : ℂ | -(j : ℝ) < s.re}` using `(hG j).analyticOnNhd (hopen _)`.

Establish `hfk : AnalyticOnNhd ℂ (G k) {s : ℂ | -(j : ℝ) < s.re}` using `((hG k).mono hsub).analyticOnNhd (hopen _)`. Establish `hpre : IsPreconnected {s : ℂ | -(j : ℝ) < s.re}` using `(convex_halfSpace_re_gt (-(j : ℝ))).isPreconnected`. Establish `h2 : (2 : ℂ) ∈ {s : ℂ | -(j : ℝ) < s.re}`. Establish `h0 : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Simplify using `only [Set.mem_setOf_eq, Complex.re_ofNat]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hev : G j =ᶠ[nhds (2 : ℂ)] G k`. Establish `hmem : {s : ℂ | (1 : ℝ) < s.re} ∈ nhds (2 : ℂ)` using `(hopen 1).mem_nhds (by simp)`. Use `filter_upwards [hmem] with s hs`. Rewrite using `[hS j s hs, hS k s hs]`.

Conclude with `hfj.eqOn_of_preconnected_of_eventuallyEq hfk hpre h2 hev`. Establish `hidx : ∀ s : ℂ, -((⌈-s.re⌉₊ + 1 : ℕ) : ℝ) < s.re`. Introduce `s`. Establish `h1 : -s.re ≤ (⌈-s.re⌉₊ : ℝ)` using `Nat.le_ceil _`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → G (⌈-s.re⌉₊ + 1) s = G k s`. Introduce `k s hs`. Break down `le_total (⌈-s.re⌉₊ + 1) k with h | h` into its components or cases. Conclude with `hagree _ _ h (hidx s)`.

Conclude with `(hagree _ _ h hs).symm`. Use `⟨fun s => G (⌈-s.re⌉₊ + 1) s, ?_, hT⟩` and prove the remaining obligations. Introduce `s`. Use `set k := ⌈-s.re⌉₊ + 1 with hk`. Establish `hs : s ∈ {w : ℂ | -(k : ℝ) < w.re}` using `hidx s`.

Establish `hnh : {w : ℂ | -(k : ℝ) < w.re} ∈ nhds s` using `(hopen _).mem_nhds hs`. Establish `hd : DifferentiableAt ℂ (G k) s` using `(hG k).differentiableAt hnh`. Use `hd.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hnh] with w hw`. Conclude with `hT k w hw`.
-/
theorem entire_of_halfPlane_continuations :
    ∀ (S : ℂ → ℂ) (G : ℕ → ℂ → ℂ), (∀ k, DifferentiableOn ℂ (G k) {s | -(k : ℝ) < s.re}) →
  (∀ k s, 1 < s.re → G k s = S s) → ∃ T : ℂ → ℂ, Differentiable ℂ T ∧ ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → T s = G k s := by
  intro S G hG hS
  have hopen : ∀ r : ℝ, IsOpen {s : ℂ | r < s.re} := fun r =>
    isOpen_lt continuous_const Complex.continuous_re

  have hagree : ∀ j k : ℕ, j ≤ k → Set.EqOn (G j) (G k) {s : ℂ | -(j : ℝ) < s.re} := by
    intro j k hjk
    have hsub : {s : ℂ | -(j : ℝ) < s.re} ⊆ {s : ℂ | -(k : ℝ) < s.re} := by
      intro s hs
      have h1 : (j : ℝ) ≤ k := by exact_mod_cast hjk
      simp only [Set.mem_setOf_eq] at hs ⊢
      linarith
    have hfj : AnalyticOnNhd ℂ (G j) {s : ℂ | -(j : ℝ) < s.re} :=
      (hG j).analyticOnNhd (hopen _)
    have hfk : AnalyticOnNhd ℂ (G k) {s : ℂ | -(j : ℝ) < s.re} :=
      ((hG k).mono hsub).analyticOnNhd (hopen _)
    have hpre : IsPreconnected {s : ℂ | -(j : ℝ) < s.re} :=
      (convex_halfSpace_re_gt (-(j : ℝ))).isPreconnected
    have h2 : (2 : ℂ) ∈ {s : ℂ | -(j : ℝ) < s.re} := by
      have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      simp only [Set.mem_setOf_eq, Complex.re_ofNat]
      linarith
    have hev : G j =ᶠ[nhds (2 : ℂ)] G k := by
      have hmem : {s : ℂ | (1 : ℝ) < s.re} ∈ nhds (2 : ℂ) :=
        (hopen 1).mem_nhds (by simp)
      filter_upwards [hmem] with s hs
      rw [hS j s hs, hS k s hs]
    exact hfj.eqOn_of_preconnected_of_eventuallyEq hfk hpre h2 hev

  have hidx : ∀ s : ℂ, -((⌈-s.re⌉₊ + 1 : ℕ) : ℝ) < s.re := by
    intro s
    have h1 : -s.re ≤ (⌈-s.re⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith

  have hT : ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → G (⌈-s.re⌉₊ + 1) s = G k s := by
    intro k s hs
    rcases le_total (⌈-s.re⌉₊ + 1) k with h | h
    · exact hagree _ _ h (hidx s)
    · exact (hagree _ _ h hs).symm
  refine ⟨fun s => G (⌈-s.re⌉₊ + 1) s, ?_, hT⟩
  intro s
  set k := ⌈-s.re⌉₊ + 1 with hk
  have hs : s ∈ {w : ℂ | -(k : ℝ) < w.re} := hidx s
  have hnh : {w : ℂ | -(k : ℝ) < w.re} ∈ nhds s := (hopen _).mem_nhds hs
  have hd : DifferentiableAt ℂ (G k) s := (hG k).differentiableAt hnh
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hnh] with w hw
  exact hT k w hw

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue
