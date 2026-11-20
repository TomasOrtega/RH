import Mathlib

namespace GlobalTheory.SpanDecay

/- English proof (translation)
Simplify using `only`. Introduce `G H _ _ ρ D c S v hS u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero => exact ⟨0, fun g => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨C1, h1⟩` from `hx`. Take `⟨C2, h2⟩` from `hy`. Use `⟨C1 + C2, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, inner_add_right, add_mul]`.

Conclude with `(norm_add_le _ _).trans (add_le_add (h1 g) (h2 g))`. Consider the case `smul a x _ hx`. Take `⟨C, h⟩` from `hx`. Use `⟨‖a‖ * C, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, inner_smul_right, norm_mul, mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left (h g) (norm_nonneg _)`.
-/
theorem span_decay : (let d1 : {G H : Type} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → (G → H →L[ℂ] H) → (G → ℝ) → ℝ → H → H → Prop := @(fun {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : G → H →L[ℂ] H) (D : G → ℝ) (c : ℝ) (v u : H) ↦ ∃ (C : ℝ), ∀ (g : G), ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))); ∀ {G H : Type} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {v : H}, (∀ u ∈ S, d1 ρ D c v u) → ∀ u ∈ Submodule.span ℂ S, d1 ρ D c v u) := by
  dsimp only
  intro G H _ _ ρ D c S v hS u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C1, h1⟩ := hx
    obtain ⟨C2, h2⟩ := hy
    refine ⟨C1 + C2, fun g => ?_⟩
    rw [map_add, inner_add_right, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 g) (h2 g))
  | smul a x _ hx =>
    obtain ⟨C, h⟩ := hx
    refine ⟨‖a‖ * C, fun g => ?_⟩
    rw [map_smul, inner_smul_right, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h g) (norm_nonneg _)

end GlobalTheory.SpanDecay
