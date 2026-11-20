import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open Polynomial PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.TfLoc

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `show σ (algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j)) = algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j)`. Conclude with `σ.commutes _`.
-/
theorem sigmaGL_incl_fixed {k E : Type*} [Field k] [Field E] [Algebra k E] {n : ℕ}
    (σ : E ≃ₐ[k] E) (γ : GL (Fin n) k) :
    sigmaGL σ (incl γ : GL (Fin n) E) = incl γ := by
  apply Units.ext
  ext i j
  show σ (algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j)) =
    algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j)
  exact σ.commutes _

/- English proof (translation)
Establish `hℓ : σ ^ Module.finrank k E = 1`. Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Conclude with `pow_card_eq_one'`. Establish `hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1`. Rewrite using `[← sigmaGL_pow, hℓ, sigmaGL_one]`.

Establish `h` using `map_twNorm_of_pow_eq_one (sigmaGL σ) hθ δ`. Establish `h' : sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ` using `h`. Rewrite `h'` using `[hN, sigmaGL_incl_fixed]`. Establish `hc : δ * (incl γ : GL (Fin n) E) = incl γ * δ`. Combine the equalities or inequalities in the displayed calculation.

Use `congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) hc` as an intermediate fact. Simplify `this` using `[Commute, SemiconjBy]`.
-/
theorem commute_of_normGL_eq {k E : Type*} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] {n : ℕ} (σ : E ≃ₐ[k] E)
    (δ : GL (Fin n) E) (γ : GL (Fin n) k) (hN : normGL σ δ = incl γ) :
    Commute (δ : Matrix (Fin n) (Fin n) E) (incl γ : GL (Fin n) E) := by
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hθ δ
  have h' : sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ := h
  rw [hN, sigmaGL_incl_fixed] at h'
  have hc : δ * (incl γ : GL (Fin n) E) = incl γ * δ := by
    calc δ * (incl γ : GL (Fin n) E) = δ * (δ⁻¹ * incl γ * δ) := by rw [← h']
      _ = incl γ * δ := by group
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) hc
  simpa [Commute, SemiconjBy] using this

/- English proof (translation)
Introduce `hA1 k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ n δ γ hN hsep`. Establish `hc` using `commute_of_normGL_eq σ δ γ hN`. Conclude with `⟨hc, hA1 E n _ hsep _ hc⟩`.
-/
theorem norm_commutes_of_separable : PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 := by
  intro hA1 k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ n δ γ hN hsep
  have hc := commute_of_normGL_eq σ δ γ hN
  exact ⟨hc, hA1 E n _ hsep _ hc⟩

end GlobalTheory.CompanionTheory.TfLoc
