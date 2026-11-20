import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.UPartBot
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace GlobalTheory.LeviFactor
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ∀ x ∈ S, ∀ y ∈ Submodule.span ℂ T, MemLp (fun g => ⟪x, σ g y⟫_ℂ) q μ`. Introduce `x hx y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact h x hx y hy`. Consider the case `zero => simpa using (MemLp.zero : MemLp (fun _ : G => (0 : ℂ)) q μ)`.

Consider the case `add y z _ _ hy hz`. Use `hy.add hz` as an intermediate fact. Simplify using `only [map_add, ContinuousLinearMap.add_apply, inner_add_right]`. Conclude with `this`. Consider the case `smul c y _ hy`.

Use `hy.const_mul c` as an intermediate fact. Simplify `this` using `[map_smul, inner_smul_right]`. Introduce `x hx y hy`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 x hx y hy`.

Consider the case `zero => simpa using (MemLp.zero : MemLp (fun _ : G => (0 : ℂ)) q μ)`. Consider the case `add x z _ _ hx hz`. Use `hx.add hz` as an intermediate fact. Simplify using `only [inner_add_left]`. Conclude with `this`.

Consider the case `smul c x _ hx`. Use `hx.const_mul ((starRingEnd ℂ) c)` as an intermediate fact. Simplify using `only [inner_smul_left]`. Conclude with `this`.
-/
theorem memLp_matrixCoeff_span
    {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (σ : G →* (V →L[ℂ] V)) (q : ENNReal) (S T : Set V)
    (h : ∀ x ∈ S, ∀ y ∈ T, MemLp (fun g => ⟪x, σ g y⟫_ℂ) q μ) :
    ∀ x ∈ Submodule.span ℂ S, ∀ y ∈ Submodule.span ℂ T, MemLp (fun g => ⟪x, σ g y⟫_ℂ) q μ := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Submodule.span ℂ T, MemLp (fun g => ⟪x, σ g y⟫_ℂ) q μ := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simpa using (MemLp.zero : MemLp (fun _ : G => (0 : ℂ)) q μ)
    | add y z _ _ hy hz =>
      have := hy.add hz
      simp only [map_add, ContinuousLinearMap.add_apply, inner_add_right]
      exact this
    | smul c y _ hy =>
      have := hy.const_mul c
      simpa [map_smul, inner_smul_right] using this
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx => exact h1 x hx y hy
  | zero => simpa using (MemLp.zero : MemLp (fun _ : G => (0 : ℂ)) q μ)
  | add x z _ _ hx hz =>
    have := hx.add hz
    simp only [inner_add_left]
    exact this
  | smul c x _ hx =>
    have := hx.const_mul ((starRingEnd ℂ) c)
    simp only [inner_smul_left]
    exact this

/- English proof (translation)
Establish `hp0 : ENNReal.ofReal p ≠ 0`. Rewrite using `[Ne, ENNReal.ofReal_eq_zero, not_le]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpt : ENNReal.ofReal p ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `hpr : (ENNReal.ofReal p).toReal = p` using `ENNReal.toReal_ofReal (by linarith)`.

Establish `hmeas : ∀ x y : V, AEStronglyMeasurable (fun g => ⟪x, σ g y⟫_ℂ) μ` using `fun x y => (continuous_const.inner (hσ.continuous_apply y)).aestronglyMeasurable`. Establish `key : ∀ x y : V, Integrable (fun g => ‖⟪x, σ g y⟫_ℂ‖ ^ p) μ ↔ MemLp (fun g => ⟪x, σ g y⟫_ℂ) (ENNReal.ofReal p) μ`. Introduce `x y`. Use `integrable_norm_rpow_iff (hmeas x y) hp0 hpt` as an intermediate fact. Rewrite `this` using `[hpr]`.

Conclude with `this`. Introduce `x hx y hy`. Rewrite using `[key]`. Conclude with `memLp_matrixCoeff_span μ σ _ S T (fun x hx y hy => (key x y).1 (h x hx y hy)) x hx y hy`.
-/
theorem integrable_norm_rpow_matrixCoeff_span
    {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (σ : G →* (V →L[ℂ] V)) (hσ : IsUnitaryRep σ) (p : ℝ) (hp : 1 ≤ p) (S T : Set V)
    (h : ∀ x ∈ S, ∀ y ∈ T, Integrable (fun g => ‖⟪x, σ g y⟫_ℂ‖ ^ p) μ) :
    ∀ x ∈ Submodule.span ℂ S, ∀ y ∈ Submodule.span ℂ T,
      Integrable (fun g => ‖⟪x, σ g y⟫_ℂ‖ ^ p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hmeas : ∀ x y : V, AEStronglyMeasurable (fun g => ⟪x, σ g y⟫_ℂ) μ := fun x y =>
    (continuous_const.inner (hσ.continuous_apply y)).aestronglyMeasurable
  have key : ∀ x y : V, Integrable (fun g => ‖⟪x, σ g y⟫_ℂ‖ ^ p) μ ↔
      MemLp (fun g => ⟪x, σ g y⟫_ℂ) (ENNReal.ofReal p) μ := by
    intro x y
    have := integrable_norm_rpow_iff (hmeas x y) hp0 hpt
    rw [hpr] at this
    exact this
  intro x hx y hy
  rw [key]
  exact memLp_matrixCoeff_span μ σ _ S T (fun x hx y hy => (key x y).1 (h x hx y hy)) x hx y hy

/- English proof (translation)
The claim follows from `@integrable_norm_rpow_matrixCoeff_span`.
-/
example : ∀ {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (σ : G →* (V →L[ℂ] V)), IsUnitaryRep σ → ∀ (p : ℝ), 1 ≤ p → ∀ (S T : Set V), (∀ x ∈ S, ∀ y ∈ T, Integrable (fun g => ‖⟪x, σ g y⟫_ℂ‖ ^ p) μ) → ∀ x ∈ Submodule.span ℂ S, ∀ y ∈ Submodule.span ℂ T, Integrable (fun g => ‖⟪x, σ g y⟫_ℂ‖ ^ p) μ := @integrable_norm_rpow_matrixCoeff_span

end GlobalTheory
