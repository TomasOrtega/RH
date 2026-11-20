import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open Filter Topology
open scoped ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

def phaseRoot (z : ℂ) : ℂ := z / ((Real.sqrt ‖z‖ : ℝ) : ℂ)

/- English proof (translation)
Unfold `phaseRoot`. Rewrite using `[norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]`. Conclude with `Real.div_sqrt`.
-/
theorem norm_phaseRoot (z : ℂ) : ‖phaseRoot z‖ = Real.sqrt ‖z‖ := by
  unfold phaseRoot
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.div_sqrt

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `z`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Establish `h0 : phaseRoot 0 = 0` using `by simp [phaseRoot]`.

Unfold `ContinuousAt`. Rewrite using `[h0, tendsto_zero_iff_norm_tendsto_zero]`. Simplify using `only [norm_phaseRoot]`. Establish `: Continuous fun w : ℂ => Real.sqrt ‖w‖` using `by fun_prop`. Simplify using `using this.tendsto 0`.

Establish `hne : ((Real.sqrt ‖z‖ : ℝ) : ℂ) ≠ 0`. Establish `: 0 < Real.sqrt ‖z‖` using `Real.sqrt_pos.mpr (norm_pos_iff.mpr hz)`. Conclude with `this.ne'` after adjusting the coercions. Establish `hc : Continuous fun w : ℂ => ((Real.sqrt ‖w‖ : ℝ) : ℂ)` using `by fun_prop`. Conclude with `continuousAt_id.div hc.continuousAt hne`.
-/
theorem continuous_phaseRoot : Continuous phaseRoot := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : phaseRoot 0 = 0 := by simp [phaseRoot]
    unfold ContinuousAt
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_phaseRoot]
    have : Continuous fun w : ℂ => Real.sqrt ‖w‖ := by fun_prop
    simpa using this.tendsto 0
  · have hne : ((Real.sqrt ‖z‖ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hz)
      exact_mod_cast this.ne'
    have hc : Continuous fun w : ℂ => ((Real.sqrt ‖w‖ : ℝ) : ℂ) := by fun_prop
    exact continuousAt_id.div hc.continuousAt hne

/- English proof (translation)
Take `⟨h', hh'⟩` from `hr (2 * m)`. Establish `h0 : Tendsto (fun y => ‖h' y‖) (cocompact ℝ) (𝓝 0)` using `tendsto_zero_iff_norm_tendsto_zero.mp (h'.zero_at_infty')`. Establish `h1 : Tendsto (fun y => Real.sqrt ‖h' y‖) (cocompact ℝ) (𝓝 0)`. Use `(Real.continuous_sqrt.tendsto 0).comp h0` as an intermediate fact. Rewrite `this` using `[Real.sqrt_zero]`.

Conclude with `this`. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Use `h1.congr fun y => ?_` and prove the remaining obligations. Rewrite using `[hh', norm_mul, norm_mul, hn, norm_pow, norm_pow, Complex.norm_real, pow_mul', Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]`.
-/
theorem tendsto_pow_mul_of_norm_sqrt {h : C₀(ℝ, ℂ)} (hr : Rapid h) {k : ℝ → ℂ}
    (hn : ∀ y, ‖k y‖ = Real.sqrt ‖h y‖) (m : ℕ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ m * k y) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨h', hh'⟩ := hr (2 * m)
  have h0 : Tendsto (fun y => ‖h' y‖) (cocompact ℝ) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (h'.zero_at_infty')
  have h1 : Tendsto (fun y => Real.sqrt ‖h' y‖) (cocompact ℝ) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at this
    exact this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h1.congr fun y => ?_
  rw [hh', norm_mul, norm_mul, hn, norm_pow, norm_pow, Complex.norm_real, pow_mul',
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/- English proof (translation)
Establish `key : ∀ m : ℕ, ∃ g : C₀(ℝ, ℂ), ∀ y, g y = (y : ℂ) ^ m * k y` using `fun m => ⟨⟨⟨fun y => (y : ℂ) ^ m * k y, by fun_prop⟩, tendsto_pow_mul_of_norm_sqrt hr hn m⟩, fun _ => rfl⟩`. Take `⟨k', hk'⟩` from `key 0`. Establish `hk : ∀ y, k' y = k y` using `fun y => by simp [hk']`. Use `⟨k', hk, fun m => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `key m`.

Conclude with `⟨g, fun y => by rw [hg, hk]⟩`.
-/
theorem exists_rapid_of_norm_sqrt {h : C₀(ℝ, ℂ)} (hr : Rapid h) {k : ℝ → ℂ} (hc : Continuous k)
    (hn : ∀ y, ‖k y‖ = Real.sqrt ‖h y‖) : ∃ k' : C₀(ℝ, ℂ), (∀ y, k' y = k y) ∧ Rapid k' := by
  have key : ∀ m : ℕ, ∃ g : C₀(ℝ, ℂ), ∀ y, g y = (y : ℂ) ^ m * k y := fun m =>
    ⟨⟨⟨fun y => (y : ℂ) ^ m * k y, by fun_prop⟩, tendsto_pow_mul_of_norm_sqrt hr hn m⟩,
      fun _ => rfl⟩
  obtain ⟨k', hk'⟩ := key 0
  have hk : ∀ y, k' y = k y := fun y => by simp [hk']
  refine ⟨k', hk, fun m => ?_⟩
  obtain ⟨g, hg⟩ := key m
  exact ⟨g, fun y => by rw [hg, hk]⟩

/- English proof (translation)
Introduce `h hr`. Take `⟨h₁, e₁, r₁⟩` from `exists_rapid_of_norm_sqrt hr (k := fun y => phaseRoot (h y)) (continuous_phaseRoot.comp h.continuous) (fun y => norm_phaseRoot _)`. Take `⟨h₂, e₂, r₂⟩` from `exists_rapid_of_norm_sqrt hr (k := fun y => ((Real.sqrt ‖h y‖ : ℝ) : ℂ)) (by have := h.continuous; fun_prop) (fun y => by rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)])`. Establish `hs : star h₂ = h₂`. Use extensionality with `y`.

Rewrite using `[ZeroAtInftyContinuousMap.star_apply, e₂]`. Simplify using the standard rewrite rules. Use `⟨h₁, h₂, r₁, r₂, by rwa [hs], ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[ZeroAtInftyContinuousMap.mul_apply, e₁, e₂]`.

Distinguish the cases in `hy : h y = 0`. Simplify using `[hy, phaseRoot]`. Establish `hne : ((Real.sqrt ‖h y‖ : ℝ) : ℂ) ≠ 0`. Establish `: 0 < Real.sqrt ‖h y‖` using `Real.sqrt_pos.mpr (norm_pos_iff.mpr hy)`. Conclude with `this.ne'` after adjusting the coercions.

Simplify using `only [phaseRoot]`. Clear the denominators using the available nonvanishing facts.
-/
theorem factorRapid : FactorRapid := by
  intro h hr
  obtain ⟨h₁, e₁, r₁⟩ := exists_rapid_of_norm_sqrt hr (k := fun y => phaseRoot (h y))
    (continuous_phaseRoot.comp h.continuous) (fun y => norm_phaseRoot _)
  obtain ⟨h₂, e₂, r₂⟩ := exists_rapid_of_norm_sqrt hr (k := fun y => ((Real.sqrt ‖h y‖ : ℝ) : ℂ))
    (by have := h.continuous; fun_prop)
    (fun y => by rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)])
  have hs : star h₂ = h₂ := by
    ext y
    rw [ZeroAtInftyContinuousMap.star_apply, e₂]
    simp
  refine ⟨h₁, h₂, r₁, r₂, by rwa [hs], ?_⟩
  ext y
  rw [ZeroAtInftyContinuousMap.mul_apply, e₁, e₂]
  by_cases hy : h y = 0
  · simp [hy, phaseRoot]
  · have hne : ((Real.sqrt ‖h y‖ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ‖h y‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hy)
      exact_mod_cast this.ne'
    simp only [phaseRoot]
    field_simp

end GlobalTheory.CompanionTheory.KerFc
