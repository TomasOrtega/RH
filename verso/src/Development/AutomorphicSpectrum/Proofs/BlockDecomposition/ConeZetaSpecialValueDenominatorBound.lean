import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominatorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeSeriesSpecialValueRationalStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.WeightSumAsFiniteDifferencesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesSummableRightHalfPlaneStatement

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Establish `hk : (0 : ℝ) < k` using `by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le p) hp)`. Establish `hpk : (p : ℝ) < k` using `by exact_mod_cast hp`. Establish `hp0 : (0 : ℝ) ≤ p` using `Nat.cast_nonneg p`. Use `set C₁ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | 0 < s.im} with hC₁`. Use `set C₂ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | s.re < 1} with hC₂`.

Establish `hO₁ : IsOpen C₁` using `(isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_im)`. Establish `hO₂ : IsOpen C₂` using `(isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)`. Establish `hV₁ : Convex ℝ C₁` using `(convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)`. Establish `hV₂ : Convex ℝ C₂` using `(convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)`. Establish `hs₁ : C₁ ⊆ {1}ᶜ`.

Introduce `s hs h1`. Establish `: s = 1` using `h1`. Establish `h2` using `hs.2`. Simplify using `[this] at h2`. Establish `hs₂ : C₂ ⊆ {1}ᶜ`.

Introduce `s hs h1`. Establish `: s = 1` using `h1`. Establish `h2` using `hs.2`. Simplify using `[this] at h2`. Establish `hAT₁ : AnalyticOnNhd ℂ T C₁` using `(hT.mono hs₁).analyticOnNhd hO₁`.

Establish `hAG₁ : AnalyticOnNhd ℂ G C₁` using `(hG.mono fun s hs => hs.1).analyticOnNhd hO₁`. Establish `hAT₂ : AnalyticOnNhd ℂ T C₂` using `(hT.mono hs₂).analyticOnNhd hO₂`. Establish `hAG₂ : AnalyticOnNhd ℂ G C₂` using `(hG.mono fun s hs => hs.1).analyticOnNhd hO₂`. Establish `hz₁ : (2 + Complex.I : ℂ) ∈ C₁`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> simp <;> linarith`.

Establish `hev₁ : T =ᶠ[nhds (2 + Complex.I : ℂ)] G`. Establish `hopen : IsOpen {s : ℂ | 1 < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Use `filter_upwards [hopen.mem_nhds (by simp : (2 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re})] with s hs`. Conclude with `h s hs`. Establish `hE₁ : Set.EqOn T G C₁` using `hAT₁.eqOn_of_preconnected_of_eventuallyEq hAG₁ hV₁.isPreconnected hz₁ hev₁`.

Establish `hz₂ : (Complex.I : ℂ) ∈ C₂`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> simp <;> linarith`. Establish `hz₂' : (Complex.I : ℂ) ∈ C₁`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> simp <;> linarith`. Establish `hev₂ : T =ᶠ[nhds (Complex.I : ℂ)] G` using `by filter_upwards [hO₁.mem_nhds hz₂'] with s hs`.

Conclude with `hE₁ hs`. Establish `hE₂ : Set.EqOn T G C₂` using `hAT₂.eqOn_of_preconnected_of_eventuallyEq hAG₂ hV₂.isPreconnected hz₂ hev₂`. Use `hE₂ ?_` and prove the remaining obligations. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_at_neg_of_eq_right (k p : ℕ) (hp : p < k) (T G : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ) (hG : DifferentiableOn ℂ G {s | -(k : ℝ) < s.re})
    (h : ∀ s : ℂ, 1 < s.re → T s = G s) : T (-(p : ℂ)) = G (-(p : ℂ)) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le p) hp)
  have hpk : (p : ℝ) < k := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set C₁ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | 0 < s.im} with hC₁
  set C₂ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | s.re < 1} with hC₂
  have hO₁ : IsOpen C₁ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hO₂ : IsOpen C₂ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hV₁ : Convex ℝ C₁ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)
  have hV₂ : Convex ℝ C₂ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hs₁ : C₁ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hs₂ : C₂ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hAT₁ : AnalyticOnNhd ℂ T C₁ := (hT.mono hs₁).analyticOnNhd hO₁
  have hAG₁ : AnalyticOnNhd ℂ G C₁ := (hG.mono fun s hs => hs.1).analyticOnNhd hO₁
  have hAT₂ : AnalyticOnNhd ℂ T C₂ := (hT.mono hs₂).analyticOnNhd hO₂
  have hAG₂ : AnalyticOnNhd ℂ G C₂ := (hG.mono fun s hs => hs.1).analyticOnNhd hO₂
  have hz₁ : (2 + Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₁ : T =ᶠ[nhds (2 + Complex.I : ℂ)] G := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re})] with s hs
    exact h s hs
  have hE₁ : Set.EqOn T G C₁ :=
    hAT₁.eqOn_of_preconnected_of_eventuallyEq hAG₁ hV₁.isPreconnected hz₁ hev₁
  have hz₂ : (Complex.I : ℂ) ∈ C₂ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hz₂' : (Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₂ : T =ᶠ[nhds (Complex.I : ℂ)] G := by
    filter_upwards [hO₁.mem_nhds hz₂'] with s hs
    exact hE₁ hs
  have hE₂ : Set.EqOn T G C₂ :=
    hAT₂.eqOn_of_preconnected_of_eventuallyEq hAG₂ hV₂.isPreconnected hz₂ hev₂
  refine hE₂ ?_
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith

/- English proof (translation)
Take `⟨Q, _, cs, u, K, hu, hc, hK, hid⟩` from `GlobalTheory.T.weighted_sum_decomposition_denominators r l (Fintype.card ι * (p + 1) + 2) w hl hw hz`. Use `set G : ℂ → ℂ := fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m with hGdef`. Establish `hG : DifferentiableOn ℂ G {s | -((p + 1 : ℕ) : ℝ) < s.re}`. Use `DifferentiableOn.fun_sum fun q _ => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb (p + 1) _ (cs q) (u q) le_rfl (hu q) (hc q)`.

Establish `hTG : ∀ s : ℂ, 1 < s.re → T s = G s`. Introduce `s hs`. Rewrite using `[← (hS s hs).tsum_eq]`. Conclude with `hid _ (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)`. Establish `hval` using `eq_at_neg_of_eq_right (p + 1) p (Nat.lt_succ_self p) T G hT hG hTG`.

Use `choose ρ ζ hρ hζ using fun q => GlobalTheory.T.cone_series_special_value_rational ι r a b (u q) (cs q) p K l hl (hK q) hp`. Use `⟨∑ q, ρ q, K, ∑ q, ζ q, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, hGdef]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun q _ => hρ q`.

Rewrite using `[Finset.mul_sum]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun q _ => hζ q`.
-/
theorem abelValue_mem_zInv (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (w : (Fin r → ℕ) → ℚ) (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i)
    (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (hz : ∀ m, ∃ z : ℤ, w m = z) (T : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ)
    (hS : ∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) (p : ℕ)
    (hp : ∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) :
    ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  obtain ⟨Q, _, cs, u, K, hu, hc, hK, hid⟩ :=
    GlobalTheory.T.weighted_sum_decomposition_denominators r l (Fintype.card ι * (p + 1) + 2) w hl hw hz
  set G : ℂ → ℂ := fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m with hGdef
  have hG : DifferentiableOn ℂ G {s | -((p + 1 : ℕ) : ℝ) < s.re} := by
    refine DifferentiableOn.fun_sum fun q _ => ?_
    exact GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb (p + 1) _ (cs q) (u q) le_rfl (hu q) (hc q)
  have hTG : ∀ s : ℂ, 1 < s.re → T s = G s := by
    intro s hs
    rw [← (hS s hs).tsum_eq]
    exact hid _ (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)
  have hval := eq_at_neg_of_eq_right (p + 1) p (Nat.lt_succ_self p) T G hT hG hTG
  choose ρ ζ hρ hζ using fun q => GlobalTheory.T.cone_series_special_value_rational ι r a b (u q) (cs q) p K l hl (hK q) hp
  refine ⟨∑ q, ρ q, K, ∑ q, ζ q, ?_, ?_⟩
  · rw [hval, hGdef]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hρ q
  · rw [Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hζ q

/- English proof (translation)
Introduce `ι _ r l a b w hr hl ha hb hw hz T hT hS p hp`. Conclude with `abelValue_mem_zInv ι r l a b w hr hl ha hb hw hz T hT hS p hp`.
-/
theorem abelValue_mem_zInv' : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r l a b w hr hl ha hb hw hz T hT hS p hp
  exact abelValue_mem_zInv ι r l a b w hr hl ha hb hw hz T hT hS p hp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
