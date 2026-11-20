import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ ℓ _`. Set `f : NumberField.RingOfIntegers F → ℚ_[ℓ] ⊗[ℚ] F` to `fun a => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F)`. Take `⟨s, hs⟩` from `(inferInstance : Module.Finite ℤ (NumberField.RingOfIntegers F)).fg_top`. Establish `hint : ∀ x ∈ (f '' (s : Set (NumberField.RingOfIntegers F))), IsIntegral ℤ_[ℓ] x`. Introduce and unpack `_ ⟨a, -, rfl⟩`.

Establish `h1 : IsIntegral ℤ ((a : F))` using `NumberField.RingOfIntegers.isIntegral_coe a`. Establish `h2 : IsIntegral ℤ (f a)`. Use `h1.map ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).restrictScalars ℤ)` as an intermediate fact. Simplify `this` using `[f]`. Conclude with `h2.tower_top`.

Establish `hfin : Module.Finite ℤ_[ℓ] (Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F))))` using `Algebra.finite_adjoin_of_finite_of_isIntegral ((s.finite_toSet).image f) hint`. Establish `heq : cenOrder ℓ F = Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, rfl⟩`.

Set `A` to `Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))`. Set `N : Submodule ℤ (NumberField.RingOfIntegers F)` to `{ carrier := {x | f x ∈ A} add_mem' := by`. Introduce `x y hx hy`. Simplify using `only [Set.mem_setOf_eq, f, map_add, TensorProduct.tmul_add] at hx hy ⊢`. Conclude with `A.add_mem hx hy`.

Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq, f, map_zero, TensorProduct.tmul_zero]`. Conclude with `A.zero_mem`. Use the proof step `smul_mem' := by`. Introduce `c x hx`.

Simplify using `only [Set.mem_setOf_eq, f, zsmul_eq_mul, map_mul, map_intCast] at hx ⊢`. Establish `: (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((c : F) * (x : F)) = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (x : F))`. Rewrite using `[← zsmul_eq_mul, TensorProduct.tmul_smul]`. Rewrite using `[this]`. Conclude with `A.toSubring.zsmul_mem hx c }`.

Establish `hsN : (s : Set _) ⊆ N` using `fun x hx => show f x ∈ A from Algebra.subset_adjoin ⟨x, hx, rfl⟩`. Establish `: a ∈ N`. Use `Submodule.span_le.mpr hsN` as an intermediate fact. Rewrite `this` using `[hs]`. Conclude with `this Submodule.mem_top`.

Conclude with `this`. Apply `Algebra.adjoin_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, -, rfl⟩`. Conclude with `⟨a, rfl⟩`. Rewrite using `[heq]`.

Conclude with `hfin`.
-/
theorem cenOrder_finite : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := by
  intro F _ _ ℓ _
  classical
  let f : NumberField.RingOfIntegers F → ℚ_[ℓ] ⊗[ℚ] F := fun a => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F)
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ (NumberField.RingOfIntegers F)).fg_top
  have hint : ∀ x ∈ (f '' (s : Set (NumberField.RingOfIntegers F))), IsIntegral ℤ_[ℓ] x := by
    rintro _ ⟨a, -, rfl⟩
    have h1 : IsIntegral ℤ ((a : F)) := NumberField.RingOfIntegers.isIntegral_coe a
    have h2 : IsIntegral ℤ (f a) := by
      have := h1.map ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).restrictScalars ℤ)
      simpa [f] using this
    exact h2.tower_top
  have hfin : Module.Finite ℤ_[ℓ] (Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral ((s.finite_toSet).image f) hint
  have heq : cenOrder ℓ F = Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F))) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      let A := Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))
      let N : Submodule ℤ (NumberField.RingOfIntegers F) :=
        { carrier := {x | f x ∈ A}
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq, f, map_add, TensorProduct.tmul_add] at hx hy ⊢
            exact A.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_setOf_eq, f, map_zero, TensorProduct.tmul_zero]
            exact A.zero_mem
          smul_mem' := by
            intro c x hx
            simp only [Set.mem_setOf_eq, f, zsmul_eq_mul, map_mul, map_intCast] at hx ⊢
            have : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((c : F) * (x : F)) = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (x : F)) := by
              rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
            rw [this]
            exact A.toSubring.zsmul_mem hx c }
      have hsN : (s : Set _) ⊆ N := fun x hx => show f x ∈ A from Algebra.subset_adjoin ⟨x, hx, rfl⟩
      have : a ∈ N := by
        have := Submodule.span_le.mpr hsN
        rw [hs] at this
        exact this Submodule.mem_top
      exact this
    · apply Algebra.adjoin_mono
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
  rw [heq]
  exact hfin

end GlobalTheory
