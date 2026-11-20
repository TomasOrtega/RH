import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `Γ _ N x y η h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `h 1 1`. Simplify using `only [map_one, toAdd_one, zero_mul, mul_one] at h0`. Take the linear combination `-h0`.

Introduce `g n`. Establish `h1` using `h g n`. Establish `h2` using `h (g * n * g⁻¹) g`. Establish `e : g * n * g⁻¹ * g = g * n` using `by group`. Establish `e2 : (x (g * n * g⁻¹)).toAdd = (x n).toAdd`.

Simplify using `only [map_mul, map_inv, toAdd_mul, toAdd_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[e, e2]`. Take the linear combination `h1 - h2`. Introduce `m n hm`.

Establish `h3` using `h m n`. Rewrite `h3` using `[hm, zero_mul]`. Take the linear combination `h3`.
-/
theorem cochain_coboundary_prod_hom_identities :
    ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
    (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
    η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
    (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  intro Γ _ N x y η h
  refine ⟨?_, ?_, ?_⟩
  · have h0 := h 1 1
    simp only [map_one, toAdd_one, zero_mul, mul_one] at h0
    linear_combination -h0
  · intro g n
    have h1 := h g n
    have h2 := h (g * n * g⁻¹) g
    have e : g * n * g⁻¹ * g = g * n := by group
    have e2 : (x (g * n * g⁻¹)).toAdd = (x n).toAdd := by
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
      ring
    rw [e, e2] at h2
    linear_combination h1 - h2
  · intro m n hm
    have h3 := h m n
    rw [hm, zero_mul] at h3
    linear_combination h3

end GlobalTheory
