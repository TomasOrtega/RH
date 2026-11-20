import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory.FN

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_im`.
-/
theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
The claim follows from `(convex_halfSpace_im_gt 0).isPreconnected`.
-/
theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

/- English proof (translation)
Rewrite using `[Filter.neBot_iff]`. Introduce `h`. Establish `h0 : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs` using `h ▸ Filter.mem_bot`. Rewrite `h0` using `[mem_codiscreteWithin_iff_forall_mem_nhdsNE]`. Establish `hI : Complex.I ∈ Hs` using `by show (0 : ℝ) < Complex.I.im; simp`.

Establish `h1` using `h0 Complex.I hI`. Rewrite `h1` using `[Set.empty_union]`. Establish `h2 : Hs ∈ 𝓝[≠] Complex.I` using `mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)`. Establish `h3 : (∅ : Set ℂ) ∈ 𝓝[≠] Complex.I`. Use `Filter.inter_mem h2 h1` as an intermediate fact.

Simplify using `using this`. Conclude with `(Filter.empty_mem_iff_bot.mp h3 ▸ (inferInstance : (𝓝[≠] Complex.I).NeBot)).ne rfl`.
-/
theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have h0 : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := h ▸ Filter.mem_bot
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h0
  have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
  have h1 := h0 Complex.I hI
  rw [Set.empty_union] at h1
  have h2 : Hs ∈ 𝓝[≠] Complex.I := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)
  have h3 : (∅ : Set ℂ) ∈ 𝓝[≠] Complex.I := by
    have := Filter.inter_mem h2 h1
    simpa using this
  exact (Filter.empty_mem_iff_bot.mp h3 ▸ (inferInstance : (𝓝[≠] Complex.I).NeBot)).ne rfl

/- English proof (translation)
Use `haveI := codiscreteWithin_Hs_neBot`. Establish `han : AnalyticOnNhd ℂ a Hs` using `ha.analyticOnNhd isOpen_Hs`. Break down `han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h` into its components or cases. Conclude with `fun z hz => h hz`. It suffices to derive a contradiction.

Establish `he : a =ᶠ[Filter.codiscreteWithin Hs] (0 : ℂ → ℂ)` using `Filter.Germ.coe_eq.mp h0`. Take `⟨z, hz1, hz2⟩` from `(h.and he).exists`. Conclude with `hz1 hz2`.
-/
theorem eqOn_zero_of_germ_eq_zero {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) = 0) :
    ∀ z ∈ Hs, a z = 0 := by
  haveI := codiscreteWithin_Hs_neBot
  have han : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h
  · exact fun z hz => h hz
  · exfalso
    have he : a =ᶠ[Filter.codiscreteWithin Hs] (0 : ℂ → ℂ) := Filter.Germ.coe_eq.mp h0
    obtain ⟨z, hz1, hz2⟩ := (h.and he).exists
    exact hz1 hz2

/- English proof (translation)
Use `haveI := codiscreteWithin_Hs_neBot`. Use `⟨inferInstance, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b ha hb hab z hz`. Establish `h0 : ((a - b : ℂ → ℂ) : Mero) = 0`. Rewrite using `[Filter.Germ.coe_sub, hab, sub_self]`.

Use `eqOn_zero_of_germ_eq_zero (ha.sub hb) h0 z hz` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Introduce `a ha hne`. Establish `han : AnalyticOnNhd ℂ a Hs` using `ha.analyticOnNhd isOpen_Hs`. Establish `hev : ∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0`.

Break down `han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Rewrite using `[← Filter.Germ.coe_zero, Filter.Germ.coe_eq]`. Use `filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz`.

Conclude with `h hz`. Conclude with `h`. Use `⟨hev, ?_⟩` and prove the remaining obligations. Use `⟨⟨(a : Mero), ((fun z => (a z)⁻¹ : ℂ → ℂ) : Mero), ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq] filter_upwards [hev] with z hz`.

Simplify using `[hz]`. Rewrite using `[← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq] filter_upwards [hev] with z hz`. Simplify using `[hz]`.
-/
theorem germ_main : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := by
  haveI := codiscreteWithin_Hs_neBot
  refine ⟨inferInstance, ?_, ?_⟩
  · intro a b ha hb hab z hz
    have h0 : ((a - b : ℂ → ℂ) : Mero) = 0 := by
      rw [Filter.Germ.coe_sub, hab, sub_self]
    have := eqOn_zero_of_germ_eq_zero (ha.sub hb) h0 z hz
    simpa [sub_eq_zero] using this
  · intro a ha hne
    have han : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
    have hev : ∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0 := by
      rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h
      · exfalso
        apply hne
        rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
        filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
        exact h hz
      · exact h
    refine ⟨hev, ?_⟩
    refine ⟨⟨(a : Mero), ((fun z => (a z)⁻¹ : ℂ → ℂ) : Mero), ?_, ?_⟩, rfl⟩
    · rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [hev] with z hz
      simp [hz]
    · rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [hev] with z hz
      simp [hz]

/- English proof (translation)
The claim follows from `germ_main`.
-/
example : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := germ_main

end GlobalTheory.FN
