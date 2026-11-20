import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' ℤ_[l] N`. Establish `hq` using `IsModuleTopology.isQuotientMap_of_surjective (R := ℤ_[l]) hπ`. Rewrite using `[← hq.isClosed_preimage]`. Take `⟨m, φ, hφ⟩` from `Module.Finite.exists_fin' ℤ_[l] (M.comap π)`. Establish `hc : Continuous (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l]))` using `IsModuleTopology.continuous_of_linearMap ((M.comap π).subtype ∘ₗ φ)`.

Establish `hrange : Set.range (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) = π ⁻¹' (M : Set N)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `(φ x).2`.

Introduce `hy`. Take `⟨x, hx⟩` from `hφ ⟨y, hy⟩`. Conclude with `⟨x, by simp [hx]⟩`. Rewrite using `[← hrange]`. Conclude with `(isCompact_range hc).isClosed`.
-/
private theorem isClosed_submodule_padicInt_finite (l : ℕ) [Fact l.Prime] {N : Type} [AddCommGroup N]
    [Module ℤ_[l] N] [Module.Finite ℤ_[l] N] [TopologicalSpace N] [IsModuleTopology ℤ_[l] N]
    (M : Submodule ℤ_[l] N) : IsClosed (M : Set N) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] N
  have hq := IsModuleTopology.isQuotientMap_of_surjective (R := ℤ_[l]) hπ
  rw [← hq.isClosed_preimage]
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[l] (M.comap π)
  have hc : Continuous (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) :=
    IsModuleTopology.continuous_of_linearMap ((M.comap π).subtype ∘ₗ φ)
  have hrange : Set.range (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) = π ⁻¹' (M : Set N) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (φ x).2
    · intro hy
      obtain ⟨x, hx⟩ := hφ ⟨y, hy⟩
      exact ⟨x, by simp [hx]⟩
  rw [← hrange]
  exact (isCompact_range hc).isClosed

/- English proof (translation)
Use `letI : TopologicalSpace R := moduleTopology ℤ_[l] R`. Use `haveI : IsModuleTopology ℤ_[l] R := ⟨rfl⟩`. Use `haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing ℤ_[l] R`. Establish `hcl : ∀ M : Submodule ℤ_[l] R, IsClosed (M : Set R)` using `fun M => isClosed_submodule_padicInt_finite l M`. Use `haveI : T2Space R := by`.

Rewrite using `[IsTopologicalAddGroup.t2Space_iff_zero_closed]`. Simplify using `using hcl ⊥`. Use `haveI : CompactSpace R := by`. Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' ℤ_[l] R`. Establish `hc : Continuous π` using `IsModuleTopology.continuous_of_linearMap π`.

Conclude with `⟨by simpa [hπ.range_eq] using isCompact_range hc⟩`. Take `⟨E, hES, hE⟩` from `exists_idempotent_in_compact_subsemigroup (fun r => continuous_mul_right r) (closure (Set.range fun n : ℕ => b ^ (n + 1))) ⟨b ^ (0 + 1), subset_closure ⟨0, rfl⟩⟩ isClosed_closure.isCompact (by`. Introduce `x hx y hy`. Use `map_mem_closure₂ (f := fun x y : R => x * y) continuous_mul hx hy ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩ _ ⟨j, rfl⟩`.

Use `⟨i + j + 1, ?_⟩` and prove the remaining obligations. Use `show b ^ (i + j + 1 + 1) = b ^ (i + 1) * b ^ (j + 1)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use the proof step `omega)`.

Use `⟨E, hE, fun M c h => ?_⟩` and prove the remaining obligations. Establish `hC : IsClosed {x : R | x - c ∈ M}` using `(hcl M).preimage (continuous_id.sub continuous_const)`. Conclude with `closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n) hC hES`.
-/
theorem exists_idempotent_sub_mem_of_pow_sub_mem (l : ℕ) [Fact l.Prime] {R : Type} [Ring R]
    [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R] (b : R) :
    ∃ E : R, E * E = E ∧ ∀ (M : Submodule ℤ_[l] R) (c : R),
      (∀ n : ℕ, b ^ (n + 1) - c ∈ M) → E - c ∈ M := by
  letI : TopologicalSpace R := moduleTopology ℤ_[l] R
  haveI : IsModuleTopology ℤ_[l] R := ⟨rfl⟩
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing ℤ_[l] R
  have hcl : ∀ M : Submodule ℤ_[l] R, IsClosed (M : Set R) := fun M => isClosed_submodule_padicInt_finite l M
  haveI : T2Space R := by
    rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
    simpa using hcl ⊥
  haveI : CompactSpace R := by
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] R
    have hc : Continuous π := IsModuleTopology.continuous_of_linearMap π
    exact ⟨by simpa [hπ.range_eq] using isCompact_range hc⟩
  obtain ⟨E, hES, hE⟩ := exists_idempotent_in_compact_subsemigroup (fun r => continuous_mul_right r)
    (closure (Set.range fun n : ℕ => b ^ (n + 1))) ⟨b ^ (0 + 1), subset_closure ⟨0, rfl⟩⟩
    isClosed_closure.isCompact (by
      intro x hx y hy
      refine map_mem_closure₂ (f := fun x y : R => x * y) continuous_mul hx hy ?_
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      refine ⟨i + j + 1, ?_⟩
      show b ^ (i + j + 1 + 1) = b ^ (i + 1) * b ^ (j + 1)
      rw [← pow_add]
      congr 1
      omega)
  refine ⟨E, hE, fun M c h => ?_⟩
  have hC : IsClosed {x : R | x - c ∈ M} := (hcl M).preimage (continuous_id.sub continuous_const)
  exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n) hC hES

end GlobalTheory
