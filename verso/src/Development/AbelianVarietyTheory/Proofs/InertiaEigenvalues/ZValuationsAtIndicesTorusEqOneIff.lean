import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValsAtApply
open GlobalTheory.UnitLemma

namespace GlobalTheory.TorusKer

/- English proof (translation)
Establish `hinv : ∀ i (x : G), Multiplicative.toAdd (w i x⁻¹) = - Multiplicative.toAdd (w i x)`. Introduce `i x`. Rewrite using `[map_inv, toAdd_inv]`. Establish `hτ : τ (t : G) = (t : G)⁻¹` using `eq_inv_of_mul_eq_one_right ((hT t).1 t.2)`. Establish `hτ' : τ ((t : G)⁻¹) = (t : G)` using `by rw [map_inv, hτ, inv_inv]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `he : ∀ j, Multiplicative.toAdd (w (e j) (t : G)) = 0`. Introduce `j`. Use `congrArg (fun y : Multiplicative (Fin r → ℤ) => Multiplicative.toAdd y j) h` as an intermediate fact.

Simplify `this` using `[valsAt_apply]`. Introduce `i`. Break down `hcov i with hi | ⟨j, hj | hj⟩` into its components or cases. Establish `h1` using `hs i (t : G)`. Rewrite `h1` using `[hi, hτ, hinv]`.

Use linear arithmetic over natural numbers and integers. Substitute `hj` using the available equality. Conclude with `he j`. Substitute `hj` using the available equality. Establish `h1` using `hs (e j) (t : G)`.

Establish `h2` using `hs (e j) ((t : G)⁻¹)`. Rewrite `h1` using `[hτ, hinv, he j]`. Rewrite `h2` using `[hτ', he j, hinv]`. Use linear arithmetic over natural numbers and integers. Introduce `h`.

Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype]`. Rewrite using `[valsAt_apply, h]`. Both sides reduce to the same expression.
-/
theorem valsAt_torus_eq_one_iff (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G)
    (hT : ∀ t, t ∈ T ↔ t * τ t = 1) (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ)
    (hs : ∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x)))
    (r : ℕ) (e : Fin r → ι) (hcov : ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) (t : T) :
    (valsAt w e).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  have hinv : ∀ i (x : G), Multiplicative.toAdd (w i x⁻¹) = - Multiplicative.toAdd (w i x) := by
    intro i x; rw [map_inv, toAdd_inv]
  have hτ : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT t).1 t.2)
  have hτ' : τ ((t : G)⁻¹) = (t : G) := by rw [map_inv, hτ, inv_inv]
  constructor
  · intro h
    have he : ∀ j, Multiplicative.toAdd (w (e j) (t : G)) = 0 := by
      intro j
      have := congrArg (fun y : Multiplicative (Fin r → ℤ) => Multiplicative.toAdd y j) h
      simpa [valsAt_apply] using this
    intro i
    rcases hcov i with hi | ⟨j, hj | hj⟩
    · have h1 := hs i (t : G)
      rw [hi, hτ, hinv] at h1
      omega
    · subst hj; exact he j
    · subst hj
      have h1 := hs (e j) (t : G)
      have h2 := hs (e j) ((t : G)⁻¹)
      rw [hτ, hinv, he j] at h1
      rw [hτ', he j, hinv] at h2
      omega
  · intro h
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [valsAt_apply, h]
    rfl

end GlobalTheory.TorusKer
