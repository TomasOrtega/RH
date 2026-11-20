import Mathlib

namespace GlobalTheory.DecayOfMemSpan

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => exact ⟨0, fun g => by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨A, hA⟩` from `hx`. Take `⟨B, hB⟩` from `hy`. Use `⟨A + B, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[inner_add_left, add_mul]`. Conclude with `(norm_add_le _ _).trans (add_le_add (hA g) (hB g))`.

Consider the case `smul a x _ hx`. Take `⟨A, hA⟩` from `hx`. Use `⟨‖a‖ * A, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hA g) (norm_nonneg a)`.
-/
theorem decay_of_mem_span {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {u : H}
    (h : ∀ v ∈ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))) :
    ∀ v ∈ Submodule.span ℂ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    refine ⟨A + B, fun g => ?_⟩
    rw [inner_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA g) (hB g))
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    refine ⟨‖a‖ * A, fun g => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA g) (norm_nonneg a)

end GlobalTheory.DecayOfMemSpan
