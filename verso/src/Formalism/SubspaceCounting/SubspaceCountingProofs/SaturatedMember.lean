import Formalism.SubspaceCounting.Statement

namespace Formalism.G0

/- English proof (translation)
Introduce `O M _ _ _ _ π hπ M' P τ hsat`. Establish `hπτ : π ^ τ ≠ 0` using `pow_ne_zero _ hπ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨⟨_, hxT⟩, hxM'⟩` from `hx`.

Rewrite `hxT`, the goal using `[Submodule.ideal_span_singleton_smul]`. Take `⟨y, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxT`. Establish `hy : y ∈ M'` using `hsat _ _ hπτ hxM'`. Conclude with `(Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hy, rfl⟩`. Use `set N := P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)`.

Set `f : (M' ⧸ Submodule.comap M'.subtype N) →ₗ[O] (M ⧸ N)` to `Submodule.mapQ _ _ M'.subtype le_rfl`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.ker_mapQ]`. Simplify using the standard rewrite rules. Conclude with `Module.length_le_of_injective f hf`.
-/
theorem saturated_member : SaturatedMember := by
  intro O M _ _ _ _ π hπ M' P τ hsat
  have hπτ : π ^ τ ≠ 0 := pow_ne_zero _ hπ
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨⟨_, hxT⟩, hxM'⟩ := hx
    rw [Submodule.ideal_span_singleton_smul] at hxT ⊢
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxT
    have hy : y ∈ M' := hsat _ _ hπτ hxM'
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hy, rfl⟩
  · set N := P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)
    let f : (M' ⧸ Submodule.comap M'.subtype N) →ₗ[O] (M ⧸ N) :=
      Submodule.mapQ _ _ M'.subtype le_rfl
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
      simp
    exact Module.length_le_of_injective f hf

end Formalism.G0
