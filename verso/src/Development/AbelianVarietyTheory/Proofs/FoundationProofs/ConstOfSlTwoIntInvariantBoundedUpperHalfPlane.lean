import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
open scoped MatrixGroups
open GlobalTheory.KZ

open UpperHalfPlane ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.KZ.LevelOne

/- English proof (translation)
Introduce `φ hd hinv hb`. Set `f : ℍ → ℂ` to `fun τ => φ τ`. Establish `hfinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ` using `fun γ τ => by`. Simplify using `only [f]`. Rewrite using `[← GlobalTheory.KZ.SiegelModel.mob_ofSL]`.

Conclude with `hinv γ τ τ.2`. Establish `hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f`. Use extensionality with `τ`. Simplify `hfinv γ τ` using `[SL_slash_apply]`. Establish `hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f`.

Rewrite using `[UpperHalfPlane.mdifferentiable_iff]`. Use `hd.congr fun z hz => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, f]`. Rewrite using `[UpperHalfPlane.ofComplex_apply_of_im_pos hz]`. Establish `hbdd : IsBoundedAtImInfty f`.

Take `⟨M, t, h⟩` from `hb`. Use `isBoundedAtImInfty_iff.2 ⟨M, t + 1, fun τ hτ => ?_⟩` and prove the remaining obligations. Conclude with `h τ τ.2 (by rw [UpperHalfPlane.coe_im]; linarith [hτ])`. Set `F : ModularForm 𝒮ℒ 0` to `{ toFun := f slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ holo' := hholo bdd_at_cusps' := fun {c} hc ↦ by`. Rewrite `hc` using `[Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]`.

Rewrite using `[OnePoint.isBoundedAt_iff_forall_SL2Z hc]`. Introduce `γ _`. Rewrite using `[hs γ]`. Conclude with `hbdd }`. Take `⟨c, hc⟩` from `ModularFormClass.levelOne_weight_zero_const F`.

Use `⟨c, fun z hz => ?_⟩` and prove the remaining obligations. Use `congrFun hc ⟨z, hz⟩` as an intermediate fact. Conclude with `this`.
-/
theorem const_of_invariant_bounded :
    ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs → (∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) →
      (∃ M t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z‖ ≤ M) → ∃ c : ℂ, ∀ z ∈ Hs, φ z = c := by
  intro φ hd hinv hb
  let f : ℍ → ℂ := fun τ => φ τ
  have hfinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ := fun γ τ => by
    simp only [f]
    rw [← GlobalTheory.KZ.SiegelModel.mob_ofSL]
    exact hinv γ τ τ.2
  have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
    ext τ; simpa [SL_slash_apply] using hfinv γ τ
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine hd.congr fun z hz => ?_
    simp only [Function.comp_apply, f]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hbdd : IsBoundedAtImInfty f := by
    obtain ⟨M, t, h⟩ := hb
    refine isBoundedAtImInfty_iff.2 ⟨M, t + 1, fun τ hτ => ?_⟩
    exact h τ τ.2 (by rw [UpperHalfPlane.coe_im]; linarith [hτ])
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := f
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
      holo' := hholo
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hs γ]
        exact hbdd }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  refine ⟨c, fun z hz => ?_⟩
  have := congrFun hc ⟨z, hz⟩
  exact this

end GlobalTheory.KZ.LevelOne
