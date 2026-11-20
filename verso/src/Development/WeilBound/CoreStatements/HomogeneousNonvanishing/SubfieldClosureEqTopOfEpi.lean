import Mathlib
open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `O F _ _ β h`. Use `set K := Subfield.closure (Set.range β) with hK`. Assume the negation of the conclusion as `hne`. Establish `key` using `h (TensorProduct K F F) Algebra.TensorProduct.includeLeftRingHom (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := F)).toRingHom (by`. Use extensionality with `o`.

Establish `ho : β o ∈ K` using `Subfield.subset_closure ⟨o, rfl⟩`. Establish `e : β o = (⟨β o, ho⟩ : K) • (1 : F)`. Rewrite using `[Subfield.smul_def, smul_eq_mul, mul_one]`. Use `show β o ⊗ₜ[K] (1 : F) = (1 : F) ⊗ₜ[K] β o`. Rewrite using `[e, TensorProduct.smul_tmul])`.

Establish `hlt : Submodule.span K {(1 : F)} < ⊤`. Rewrite using `[lt_top_iff_ne_top]`. Introduce `ht`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Establish `hx : x ∈ Submodule.span K {(1 : F)}` using `ht ▸ Submodule.mem_top`. Take `⟨k, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Rewrite using `[Subfield.smul_def, smul_eq_mul, mul_one]`. Conclude with `k.2`.

Take `⟨φ, hφ0, hφ⟩` from `Submodule.exists_le_ker_of_lt_top _ hlt`. Establish `h1 : φ 1 = 0` using `hφ (Submodule.mem_span_singleton_self 1)`. Apply `hφ0` to reduce the goal to its premises. Use extensionality with `b`. Establish `e : b ⊗ₜ[K] (1 : F) = (1 : F) ⊗ₜ[K] b` using `RingHom.congr_fun key b`.

Establish `e2` using `congrArg (fun z => TensorProduct.lid K F (TensorProduct.map φ LinearMap.id z)) e`. Simplify using `only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, h1, zero_smul] at e2`. Break down `smul_eq_zero.1 e2 with h | h` into its components or cases. Simplify using `using h`. Conclude with `absurd h one_ne_zero`.
-/
theorem subfield_closure_eq_top_of_epi : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F), (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) → Subfield.closure (Set.range β) = ⊤ := by
  intro O F _ _ β h
  set K := Subfield.closure (Set.range β) with hK
  by_contra hne
  have key := h (TensorProduct K F F) Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := F)).toRingHom (by
      ext o
      have ho : β o ∈ K := Subfield.subset_closure ⟨o, rfl⟩
      have e : β o = (⟨β o, ho⟩ : K) • (1 : F) := by
        rw [Subfield.smul_def, smul_eq_mul, mul_one]
      show β o ⊗ₜ[K] (1 : F) = (1 : F) ⊗ₜ[K] β o
      rw [e, TensorProduct.smul_tmul])
  have hlt : Submodule.span K {(1 : F)} < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro ht
    apply hne
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span K {(1 : F)} := ht ▸ Submodule.mem_top
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Subfield.smul_def, smul_eq_mul, mul_one]
    exact k.2
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have h1 : φ 1 = 0 := hφ (Submodule.mem_span_singleton_self 1)
  apply hφ0
  ext b
  have e : b ⊗ₜ[K] (1 : F) = (1 : F) ⊗ₜ[K] b := RingHom.congr_fun key b
  have e2 := congrArg (fun z => TensorProduct.lid K F (TensorProduct.map φ LinearMap.id z)) e
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, h1, zero_smul] at e2
  rcases smul_eq_zero.1 e2 with h | h
  · simpa using h
  · exact absurd h one_ne_zero

end PositivityTheory.UnitarySelfGeneration
