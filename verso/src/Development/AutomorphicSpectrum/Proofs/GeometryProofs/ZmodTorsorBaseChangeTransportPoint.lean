import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, ⟨u, rfl⟩, ⟨v, hv⟩⟩`. Use `⟨u, IsUnit.of_mul_eq_one v (h.inj p ?_), rfl⟩` and prove the remaining obligations. Rewrite using `[map_mul, hv, map_one, mul_inv_cancel₀ h0]`. Introduce and unpack `⟨u, ⟨w, rfl⟩, rfl⟩`.

Use `⟨(w.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(w⁻¹ : _ˣ), ?_⟩⟩` and prove the remaining obligations. Conclude with `map_units_inv _ w`.
-/
theorem unitAt_iff_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ u, IsUnit u ∧ genMap ξ p u = a := by
  constructor
  · rintro ⟨h0, ⟨u, rfl⟩, ⟨v, hv⟩⟩
    refine ⟨u, IsUnit.of_mul_eq_one v (h.inj p ?_), rfl⟩
    rw [map_mul, hv, map_one, mul_inv_cancel₀ h0]
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(w⁻¹ : _ˣ), ?_⟩⟩
    exact map_units_inv _ w

end GlobalTheory.CompanionTheory.Ar
