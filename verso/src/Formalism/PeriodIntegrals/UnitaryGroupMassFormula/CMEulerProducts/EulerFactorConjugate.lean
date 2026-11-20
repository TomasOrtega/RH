import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.StepRegroup

open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hFE`. Take `⟨hE, hR⟩` from `hFE`. Set `σ : 𝓞 E ≃+* 𝓞 E` to `RingOfIntegers.mapRingEquiv (starRingAut (R := E))`. Establish `hσ : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (σ x) = star (algebraMap (𝓞 E) E x)` using `fun x => rfl`. Establish `hσσ : ∀ x : 𝓞 E, σ (σ x) = x`.

Introduce `x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (σ (σ x)) = algebraMap (𝓞 E) E x`. Rewrite using `[hσ, hσ, star_star]`. Use `⟨σ, hσ, hσσ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `P`. Unfold `conjIdeal`. Express the relevant statement in the definitionally equal form `_ = Ideal.span (σ '' P)`. Use `congr 1`. Use extensionality with `r`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hrs⟩`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (σ s) = algebraMap (𝓞 E) E r`.

Rewrite using `[hσ, hrs]`. Introduce and unpack `⟨s, hs, rfl⟩`. Conclude with `⟨s, hs, hσ s⟩`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `hfix : algebraMap (𝓞 E) E x ∈ {a : E | star a = a}`. Express the relevant statement in the definitionally equal form `star (algebraMap (𝓞 E) E x) = algebraMap (𝓞 E) E x`. Rewrite using `[← hσ, hx]`. Rewrite `hfix` using `[← hR]`.

Take `⟨y, hy⟩` from `hfix`. Establish `hyint : IsIntegral ℤ y`. Establish `h1 : IsIntegral ℤ ((algebraMap F E).toIntAlgHom y)`. Rewrite using `[RingHom.toIntAlgHom_coe, hy]`. Conclude with `RingOfIntegers.isIntegral_coe x`.

Conclude with `(isIntegral_algHom_iff _ (algebraMap F E).injective).mp h1`. Use `⟨⟨y, hyint⟩, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `hy`. Introduce and unpack `⟨z, rfl⟩`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (σ (algebraMap (𝓞 F) (𝓞 E) z)) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z)`. Rewrite using `[hσ]`. Establish `hmem : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) ∈ Set.range (algebraMap F E)` using `⟨(z : F), rfl⟩`. Rewrite `hmem` using `[hR]`.

Conclude with `hmem`. Introduce `P hP`. Take `⟨θ, t, ht, hθt⟩` from `hE.2.2 P hP`. Use `⟨θ, ?_⟩` and prove the remaining obligations. Establish `: σ θ = t`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (σ θ) = algebraMap (𝓞 E) E t`. Rewrite using `[hσ, ht]`. Rewrite using `[this]`. Conclude with `hθt`.
-/
theorem euler_factor_conjugate : StepConj := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨hE, hR⟩ := hFE
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut (R := E))
  have hσ : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (σ x) = star (algebraMap (𝓞 E) E x) := fun x => rfl
  have hσσ : ∀ x : 𝓞 E, σ (σ x) = x := by
    intro x
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E (σ (σ x)) = algebraMap (𝓞 E) E x
    rw [hσ, hσ, star_star]
  refine ⟨σ, hσ, hσσ, ?_, ?_, ?_⟩
  · intro P
    unfold conjIdeal
    change _ = Ideal.span (σ '' P)
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, hrs⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ s) = algebraMap (𝓞 E) E r
      rw [hσ, hrs]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, hσ s⟩
  · intro x
    constructor
    · intro hx
      have hfix : algebraMap (𝓞 E) E x ∈ {a : E | star a = a} := by
        change star (algebraMap (𝓞 E) E x) = algebraMap (𝓞 E) E x
        rw [← hσ, hx]
      rw [← hR] at hfix
      obtain ⟨y, hy⟩ := hfix
      have hyint : IsIntegral ℤ y := by
        have h1 : IsIntegral ℤ ((algebraMap F E).toIntAlgHom y) := by
          rw [RingHom.toIntAlgHom_coe, hy]
          exact RingOfIntegers.isIntegral_coe x
        exact (isIntegral_algHom_iff _ (algebraMap F E).injective).mp h1
      refine ⟨⟨y, hyint⟩, ?_⟩
      apply RingOfIntegers.ext
      exact hy
    · rintro ⟨z, rfl⟩
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ (algebraMap (𝓞 F) (𝓞 E) z)) =
        algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z)
      rw [hσ]
      have hmem : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) ∈ Set.range (algebraMap F E) :=
        ⟨(z : F), rfl⟩
      rw [hR] at hmem
      exact hmem
  · intro P hP
    obtain ⟨θ, t, ht, hθt⟩ := hE.2.2 P hP
    refine ⟨θ, ?_⟩
    have : σ θ = t := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ θ) = algebraMap (𝓞 E) E t
      rw [hσ, ht]
    rw [this]
    exact hθt

end CMEul
