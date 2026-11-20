import Mathlib

/- English proof (translation)
Introduce `F M Ω _ _ _ _ _ _ _ g`. Set `b` to `Module.finBasis ℚ M`. Establish `h : IntermediateField.adjoin F (Set.range (⇑g : M → Ω)) = IntermediateField.adjoin F (Set.range (fun i => g (b i)))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_le_iff]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[← b.sum_repr x, map_sum]`. Use `sum_mem (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Rat.smul_def, map_mul, map_ratCast]`. Conclude with `mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)`.

Apply `IntermediateField.adjoin.mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨_, rfl⟩`. Rewrite using `[h]`. Use `haveI : Finite (Set.range (fun i => g (b i))) := Set.finite_range _`.

Conclude with `IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)`.
-/
theorem UpperTheory.Reformulated.B.Qh44.ex_comp :
    ∀ {F M Ω : Type} [inst : Field F] [NumberField F] [inst_2 : Field M]
    [NumberField M] [inst_4 : Field Ω] [inst_5 : Algebra F Ω] [Algebra.IsAlgebraic F Ω] (g : M →+* Ω),
    FiniteDimensional F ↥(IntermediateField.adjoin F (Set.range (⇑g : M → Ω))) := by
  intro F M Ω _ _ _ _ _ _ _ g
  let b := Module.finBasis ℚ M
  have h : IntermediateField.adjoin F (Set.range (⇑g : M → Ω))
      = IntermediateField.adjoin F (Set.range (fun i => g (b i))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      rw [← b.sum_repr x, map_sum]
      refine sum_mem (fun i _ => ?_)
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem _ _)
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨i, rfl⟩
      exact ⟨_, rfl⟩
  rw [h]
  haveI : Finite (Set.range (fun i => g (b i))) := Set.finite_range _
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
