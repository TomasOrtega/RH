import Mathlib

namespace GlobalTheory.TargetStatementBis

open NumberField

/- English proof (translation)
Establish `hv : v ∈ Submodule.span K (Λ : Set V)` using `h ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨d₁, hd₁, h₁⟩` from `hx`. Take `⟨d₂, hd₂, h₂⟩` from `hy`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Λ.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `Λ.smul_mem _ h₁`. Rewrite using `[mul_smul]`. Conclude with `Λ.smul_mem _ h₂`. Consider the case `smul c x _ hx`.

Take `⟨d, hd, h₁⟩` from `hx`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 K)) c`. Use `⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero b.2), ?_⟩` and prove the remaining obligations. Establish `key : ((b : 𝓞 K)) • (c • x) = a • x`. Rewrite using `[← algebraMap_smul K (b : 𝓞 K) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]`.

Rewrite using `[mul_smul, key, smul_comm d a x]`. Conclude with `Λ.smul_mem a h₁`.
-/
theorem main {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V)
    (h : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set V) := h ▸ Submodule.mem_top
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
    obtain ⟨d, hd, h₁⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) c
    refine ⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero b.2), ?_⟩
    have key : ((b : 𝓞 K)) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : 𝓞 K) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, key, smul_comm d a x]
    exact Λ.smul_mem a h₁

/- English proof (translation)
Introduce `Λ h v` and use `main Λ h v`.
-/
theorem target : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V] (Λ : Submodule (NumberField.RingOfIntegers K) V), Submodule.span K (↑Λ : Set V) = ⊤ → ∀ (v : V), ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ Λ :=
  fun Λ h v => main Λ h v

end GlobalTheory.TargetStatementBis
