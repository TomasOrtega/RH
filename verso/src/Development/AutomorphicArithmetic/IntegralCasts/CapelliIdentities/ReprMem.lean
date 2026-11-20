import Mathlib

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

/- English proof (translation)
Introduce `F E _ _ _ t c h x hx`. Establish `hint : IsIntegral F t`. Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `isIntegral_algebraMap`.

Establish `hx' : x ∈ Algebra.adjoin F {t}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Conclude with `hx`. Use `clear hx`. Proceed by induction on `hx' using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Conclude with `⟨0, 1, by simp [hy]⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, b, rfl⟩` from `hy`. Take `⟨a', b', rfl⟩` from `hz`. Conclude with `⟨a + a', b + b', by rw [map_add, map_add]; ring⟩`. Consider the case `mul y z _ _ hy hz`. Take `⟨a, b, rfl⟩` from `hy`.

Take `⟨a', b', rfl⟩` from `hz`. Use `⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul]`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.ReprMem.repr_mem :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
    [inst_2 : Algebra F E] (t : E) (c : F),
    t ^ (2 : ℕ) = (Algebra.algebraMap F E : F → E) c →
      ∀ x ∈ F⟮t⟯, ∃ (a : F) (b : F), x = (Algebra.algebraMap F E : F → E) a + (Algebra.algebraMap F E : F → E) b * t := by
  intro F E _ _ _ t c h x hx
  have hint : IsIntegral F t := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [h]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin F {t} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩
    simp only [map_add, map_mul]
    rw [← h]
    ring
