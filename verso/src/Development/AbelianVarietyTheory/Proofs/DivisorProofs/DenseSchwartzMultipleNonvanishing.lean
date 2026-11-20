import Mathlib
open SchwartzMap

namespace GlobalTheory

/- English proof (translation)
Use `hd.mono ?_` and prove the remaining obligations. Introduce `φ hφ`. Establish `hφ' : HasCompactSupport (⇑φ)` using `hφ`. Establish `hinv : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x)⁻¹)`. Rewrite using `[contDiff_iff_contDiffAt]`.

Introduce `x`. Establish `h1 : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => z⁻¹) (g x)` using `contDiffAt_inv ℂ (hg x)`. Conclude with `(h1.restrict_scalars ℝ).comp x (g.smooth ⊤).contDiffAt`. Establish `hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * (g x)⁻¹)` using `(φ.smooth ⊤).mul hinv`. Establish `hc : HasCompactSupport (fun x => φ x * (g x)⁻¹)` using `hφ'.mul_right`.

Use `⟨hc.toSchwartzMap hs, fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ x = φ x * (g x)⁻¹ * g x`. Rewrite using `[mul_assoc, inv_mul_cancel₀ (hg x), mul_one]`.
-/
theorem dense_schwartz_mul_of_ne_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (g : SchwartzMap V ℂ) (hg : ∀ x, g x ≠ 0)
    (hd : Dense {φ : SchwartzMap V ℂ | HasCompactSupport (⇑φ)}) :
    Dense {F : SchwartzMap V ℂ | ∃ ψ : SchwartzMap V ℂ, ∀ x, F x = ψ x * g x} := by
  refine hd.mono ?_
  intro φ hφ
  have hφ' : HasCompactSupport (⇑φ) := hφ
  have hinv : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have h1 : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => z⁻¹) (g x) := contDiffAt_inv ℂ (hg x)
    exact (h1.restrict_scalars ℝ).comp x (g.smooth ⊤).contDiffAt
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * (g x)⁻¹) := (φ.smooth ⊤).mul hinv
  have hc : HasCompactSupport (fun x => φ x * (g x)⁻¹) := hφ'.mul_right
  refine ⟨hc.toSchwartzMap hs, fun x => ?_⟩
  change φ x = φ x * (g x)⁻¹ * g x
  rw [mul_assoc, inv_mul_cancel₀ (hg x), mul_one]

end GlobalTheory
