import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def LocalNormalIndex.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    ∀ [IsFractionRing O L] (m : Ideal O) [m.IsMaximal],
      (Localization.subalgebra.ofField L m.primeCompl
          m.primeCompl_le_nonZeroDivisors).toSubring.toAddSubgroup.relIndex
        (integralClosure (Localization.subalgebra.ofField L m.primeCompl
          m.primeCompl_le_nonZeroDivisors) L).toSubring.toAddSubgroup ≠ 0

/- English proof (translation)
Set `e : (⊥ : Subalgebra ℤ ℚ) ≃ₐ[ℤ] ℤ` to `Algebra.botEquivOfInjective Int.cast_injective`. Establish `hft : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ ℚ)` using `Algebra.FiniteType.equiv inferInstance e.symm`. Establish `hfr : IsFractionRing (⊥ : Subalgebra ℤ ℚ) ℚ`. Use `IsFractionRing.of_field (⊥ : Subalgebra ℤ ℚ) ℚ fun z ↦ ⟨algebraMap ℤ _ z.num, algebraMap ℤ _ z.den, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.

Simplify using `[Rat.num_div_den]`. Take `⟨m, hm, -⟩` from `Ideal.exists_le_maximal (⊥ : Ideal (⊥ : Subalgebra ℤ ℚ)) bot_ne_top`. Conclude with `⟨⊥, m, hft, hfr, hm⟩`.
-/
example : ∃ (O : Subalgebra ℤ ℚ) (m : Ideal O), Algebra.FiniteType ℤ O ∧
    IsFractionRing O ℚ ∧ m.IsMaximal := by
  let e : (⊥ : Subalgebra ℤ ℚ) ≃ₐ[ℤ] ℤ := Algebra.botEquivOfInjective Int.cast_injective
  have hft : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ ℚ) := Algebra.FiniteType.equiv inferInstance e.symm
  have hfr : IsFractionRing (⊥ : Subalgebra ℤ ℚ) ℚ := by
    refine IsFractionRing.of_field (⊥ : Subalgebra ℤ ℚ) ℚ fun z ↦ ⟨algebraMap ℤ _ z.num, algebraMap ℤ _ z.den, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    simp [Rat.num_div_den]
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (⊥ : Subalgebra ℤ ℚ)) bot_ne_top
  exact ⟨⊥, m, hft, hfr, hm⟩

end GroundTheory.Heights₂.Heights
