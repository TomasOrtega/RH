import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero

namespace GlobalTheory.DZA.OrbSupp

open GlobalTheory.BCT

variable {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises. Unfold `twOrb`. Simplify using `only [hc]`.

Simplify using `[avg]`.
-/
theorem exists_twConj_ne_zero (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) :
    ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold twOrb
  simp only [hc]
  simp [avg]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨x, hx⟩` from `exists_twConj_ne_zero θ K δ f hne`. Conclude with `hx (h x)`.
-/
theorem twOrb_eq_zero_of_forall (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (h : ∀ x, f (x⁻¹ * δ * θ x) = 0) : twOrb θ K δ f = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := exists_twConj_ne_zero θ K δ f hne
  exact hx (h x)

/- English proof (translation)
The claim follows from `exists_twConj_ne_zero (MonoidHom.id G) K γ f h`.
-/
theorem exists_conj_ne_zero (K : Subgroup G) (γ : G) (f : G → ℂ) (h : twOrb (MonoidHom.id G) K γ f ≠ 0) :
    ∃ x, f (x⁻¹ * γ * x) ≠ 0 :=
  exists_twConj_ne_zero (MonoidHom.id G) K γ f h

/- English proof (translation)
The claim follows from `twOrb_eq_zero_of_forall (MonoidHom.id G) K γ f h`.
-/
theorem twOrb_id_eq_zero_of_forall (K : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    twOrb (MonoidHom.id G) K γ f = 0 :=
  twOrb_eq_zero_of_forall (MonoidHom.id G) K γ f h

/- English proof (translation)
The claim follows from `exists_ne_zero_of_twOrb_ne_zero θ K δ f h`.
-/
example (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) :
    ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := exists_ne_zero_of_twOrb_ne_zero θ K δ f h

end GlobalTheory.DZA.OrbSupp
