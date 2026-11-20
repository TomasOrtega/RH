import Mathlib
namespace GlobalTheory.LatticeBoundedAction

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨d₁, hd₁, h₁⟩` from `hx`. Take `⟨d₂, hd₂, h₂⟩` from `hy`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Λ.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `Λ.smul_mem _ h₁`. Rewrite using `[mul_smul]`. Conclude with `Λ.smul_mem _ h₂`. Consider the case `smul c x _ hx`.

Take `⟨d, hd, h⟩` from `hx`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors R) c`. Establish `hb : (b : R) ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Establish `key : (b : R) • (c • x) = a • x`. Rewrite using `[← smul_assoc, Algebra.smul_def, ← hab, mul_comm, IsLocalization.mk'_spec, algebraMap_smul]`.

Use `⟨d * b, mul_ne_zero hd hb, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, key, smul_comm]`. Conclude with `Λ.smul_mem a h`.
-/
theorem main {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) :
    ∀ v ∈ Submodule.span K (↑Λ : Set V), ∃ (d : R), d ≠ (0 : R) ∧ d • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
    have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have key : (b : R) • (c • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, ← hab, mul_comm, IsLocalization.mk'_spec, algebraMap_smul]
    refine ⟨d * b, mul_ne_zero hd hb, ?_⟩
    rw [mul_smul, key, smul_comm]
    exact Λ.smul_mem a h

end GlobalTheory.LatticeBoundedAction
