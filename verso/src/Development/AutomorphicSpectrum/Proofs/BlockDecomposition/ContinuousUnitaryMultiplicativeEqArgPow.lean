import Mathlib
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary

namespace GlobalTheory.CompanionTheory.KlocOp

/- English proof (translation)
Introduce `φ hmul hc hn h1`. Establish `hmem : ∀ z : ℂˣ, φ (z : ℂ) ∈ Submonoid.unitSphere ℂ` using `fun z => by`. Simplify `hn z z.ne_zero` using `[Submonoid.unitSphere]`. Set `f : ℂˣ → Circle` to `fun z => ⟨φ (z : ℂ), hmem z⟩`. Establish `hfc : Continuous f`.

Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `hc.comp_continuous Units.continuous_val fun z => z.ne_zero`. Establish `hf1 : f 1 = 1`. Apply `Circle.ext` to reduce the goal to its premises. Use `h1 1 one_pos` as an intermediate fact.

Simplify `this` using `[f]`. Establish `hfm : ∀ a b : ℂˣ, f (a * b) = f a * f b` using `fun a b => by`. Apply `Circle.ext` to reduce the goal to its premises. Rewrite using `[Circle.coe_mul]`. Express the relevant statement in the definitionally equal form `φ ((a * b : ℂˣ) : ℂ) = φ (a : ℂ) * φ (b : ℂ)`.

Rewrite using `[Units.val_mul]`. Conclude with `hmul a b a.ne_zero b.ne_zero`. Set `χ : ℂˣ →ₜ* Circle` to `{ toFun := f, map_one' := hf1, map_mul' := hfm, continuous_toFun := hfc }`. Take `⟨⟨m, τ⟩, hp, -⟩` from `GroundTheory.Global.existsUnique_complexUnits_circle χ`. Establish `hp' : ∀ z : ℂˣ, φ (z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)` using `hp`.

Establish `hr : ∀ r : ℝ, 0 < r → (r : ℂ) ^ ((τ : ℂ) * Complex.I) = 1`. Introduce `r hr0`. Establish `hne : (r : ℂ) ≠ 0` using `by exact_mod_cast hr0.ne'`. Establish `h` using `hp' (Units.mk0 (r : ℂ) hne)`. Rewrite `h` using `[Units.val_mk0, h1 r hr0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, div_self hne, one_zpow, one_mul]`.

Conclude with `h.symm`. Use `⟨m, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h` using `hp' (Units.mk0 z hz)`. Rewrite `h` using `[Units.val_mk0, hr _ (norm_pos_iff.mpr hz), mul_one]`. Conclude with `h`.
-/
theorem cstar_char_eq_zpow : ∀ φ : ℂ → ℂ, (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → φ (z * w) = φ z * φ w) →
    ContinuousOn φ {z : ℂ | z ≠ 0} → (∀ z : ℂ, z ≠ 0 → ‖φ z‖ = 1) →
    (∀ r : ℝ, 0 < r → φ (r : ℂ) = 1) →
    ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → φ z = (z / (‖z‖ : ℂ)) ^ k := by
  intro φ hmul hc hn h1
  have hmem : ∀ z : ℂˣ, φ (z : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere] using hn z z.ne_zero
  let f : ℂˣ → Circle := fun z => ⟨φ (z : ℂ), hmem z⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact hc.comp_continuous Units.continuous_val fun z => z.ne_zero
  have hf1 : f 1 = 1 := by
    apply Circle.ext
    have := h1 1 one_pos
    simpa [f] using this
  have hfm : ∀ a b : ℂˣ, f (a * b) = f a * f b := fun a b => by
    apply Circle.ext
    rw [Circle.coe_mul]
    change φ ((a * b : ℂˣ) : ℂ) = φ (a : ℂ) * φ (b : ℂ)
    rw [Units.val_mul]
    exact hmul a b a.ne_zero b.ne_zero
  let χ : ℂˣ →ₜ* Circle :=
    { toFun := f, map_one' := hf1, map_mul' := hfm, continuous_toFun := hfc }
  obtain ⟨⟨m, τ⟩, hp, -⟩ := GroundTheory.Global.existsUnique_complexUnits_circle χ
  have hp' : ∀ z : ℂˣ, φ (z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := hp
  have hr : ∀ r : ℝ, 0 < r → (r : ℂ) ^ ((τ : ℂ) * Complex.I) = 1 := by
    intro r hr0
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have h := hp' (Units.mk0 (r : ℂ) hne)
    rw [Units.val_mk0, h1 r hr0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_self hne, one_zpow, one_mul] at h
    exact h.symm
  refine ⟨m, fun z hz => ?_⟩
  have h := hp' (Units.mk0 z hz)
  rw [Units.val_mk0, hr _ (norm_pos_iff.mpr hz), mul_one] at h
  exact h

end GlobalTheory.CompanionTheory.KlocOp
