import Mathlib

namespace GlobalTheory.SpanSingleInlMembership

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, hj, rfl⟩` from `hx`.

Use `⟨fun k => by simp, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hne : k ≠ j` using `fun e => hk (e ▸ hj)`. Simplify using `[hne]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Conclude with `⟨fun k => by simp [hx.1 k, hy.1 k], fun k hk => by simp [hx.2 k hk, hy.2 k hk]⟩`. Consider the case `smul a x _ hx`. Conclude with `⟨fun k => by simp [hx.1 k], fun k hk => by simp [hx.2 k hk]⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `hu : u = ∑ k ∈ S, u (Sum.inl k) • (Pi.single (Sum.inl k) (1 : ℤ) : Fin g ⊕ Fin g → ℤ)`.

Use function extensionality and compare the values at `i`. Break down `i with j | j` into its components or cases. Distinguish the cases in `hj : j ∈ S`. Simplify using `[Finset.sum_apply, Pi.single_apply, hj]`. Simplify using `[Finset.sum_apply, Pi.single_apply, hj, h2 j hj]`.

Simplify using `[Finset.sum_apply, h1 j]`. Rewrite using `[hu]`. Conclude with `Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)`.
-/
theorem mem_span_single_inl_iff {g : ℕ} (S : Finset (Fin g)) (u : Fin g ⊕ Fin g → ℤ) :
    u ∈ Submodule.span ℤ ((fun (k : Fin g) ↦ Pi.single (Sum.inl k) (1 : ℤ)) '' (↑S : Set (Fin g))) ↔
      (∀ (k : Fin g), u (Sum.inr k) = (0 : ℤ)) ∧ ∀ k ∉ S, u (Sum.inl k) = (0 : ℤ) := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨fun k => by simp, fun k hk => ?_⟩
      have hne : k ≠ j := fun e => hk (e ▸ hj)
      simp [hne]
    | zero => simp
    | add x y _ _ hx hy =>
      exact ⟨fun k => by simp [hx.1 k, hy.1 k], fun k hk => by simp [hx.2 k hk, hy.2 k hk]⟩
    | smul a x _ hx =>
      exact ⟨fun k => by simp [hx.1 k], fun k hk => by simp [hx.2 k hk]⟩
  · rintro ⟨h1, h2⟩
    have hu : u = ∑ k ∈ S, u (Sum.inl k) • (Pi.single (Sum.inl k) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) := by
      funext i
      rcases i with j | j
      · by_cases hj : j ∈ S
        · simp [Finset.sum_apply, Pi.single_apply, hj]
        · simp [Finset.sum_apply, Pi.single_apply, hj, h2 j hj]
      · simp [Finset.sum_apply, h1 j]
    rw [hu]
    exact Submodule.sum_mem _ fun k hk =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.SpanSingleInlMembership
