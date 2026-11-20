import Mathlib

namespace UpperTheory.Reformulated.B.FinitelyGeneratedModPow

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, by simp⟩⟩`. Consider the case `succ n ih`. Take `⟨N, hN, hx⟩` from `ih`. Take `⟨s, hs⟩ : (m ^ n).FG` from `IsNoetherian.noetherian (m ^ n)`.

Establish `key : ∀ z ∈ Ideal.span (s : Set A), ∃ w ∈ Submodule.span O (s : Set A), z - w ∈ m ^ (n + 1)`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => exact ⟨z, Submodule.subset_span hz, by simp⟩`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`.

Consider the case `add z₁ z₂ _ _ h₁ h₂`. Take `⟨w₁, hw₁, e₁⟩` from `h₁`. Take `⟨w₂, hw₂, e₂⟩` from `h₂`. Use `⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩` and prove the remaining obligations. Establish `: z₁ + z₂ - (w₁ + w₂) = (z₁ - w₁) + (z₂ - w₂)` using `by ring`.

Rewrite using `[this]`. Conclude with `Ideal.add_mem _ e₁ e₂`. Consider the case `smul a z hz h`. Take `⟨w, hw, e⟩` from `h`. Take `⟨c, hc⟩` from `hres a`.

Establish `hz' : z ∈ m ^ n` using `by rw [← hs]; exact hz`. Use `⟨c • w, Submodule.smul_mem _ c hw, ?_⟩` and prove the remaining obligations. Establish `: a • z - c • w = z * (a - algebraMap O A c) + algebraMap O A c * (z - w)`. Rewrite using `[smul_eq_mul, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Use `Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ e)` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hz' hc`. Use `⟨N ⊔ Submodule.span O (s : Set A), hN.sup ⟨s, rfl⟩, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨y, hy, hxy⟩` from `hx x`. Rewrite `hxy` using `[← hs]`. Take `⟨w, hw, e⟩` from `key _ hxy`. Use `⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_sub]` and apply the resulting hypothesis.
-/
theorem fg_mod_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n := by
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, by simp⟩⟩
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z ∈ Ideal.span (s : Set A),
        ∃ w ∈ Submodule.span O (s : Set A), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact ⟨z, Submodule.subset_span hz, by simp⟩
      | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
      | add z₁ z₂ _ _ h₁ h₂ =>
        obtain ⟨w₁, hw₁, e₁⟩ := h₁
        obtain ⟨w₂, hw₂, e₂⟩ := h₂
        refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩
        have : z₁ + z₂ - (w₁ + w₂) = (z₁ - w₁) + (z₂ - w₂) := by ring
        rw [this]
        exact Ideal.add_mem _ e₁ e₂
      | smul a z hz h =>
        obtain ⟨w, hw, e⟩ := h
        obtain ⟨c, hc⟩ := hres a
        have hz' : z ∈ m ^ n := by rw [← hs]; exact hz
        refine ⟨c • w, Submodule.smul_mem _ c hw, ?_⟩
        have : a • z - c • w = z * (a - algebraMap O A c) + algebraMap O A c * (z - w) := by
          rw [smul_eq_mul, Algebra.smul_def]; ring
        rw [this]
        refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ e)
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' hc
    refine ⟨N ⊔ Submodule.span O (s : Set A), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, e⟩ := key _ hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rwa [← sub_sub]

end UpperTheory.Reformulated.B.FinitelyGeneratedModPow
