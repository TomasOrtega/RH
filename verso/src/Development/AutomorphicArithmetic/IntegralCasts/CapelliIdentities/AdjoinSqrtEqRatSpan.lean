import Mathlib

/- English proof (translation)
Introduce `E _ _ d s hs x hx`. Establish `hint : IsIntegral ℚ s`. Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Rewrite using `[hs]`. Establish `h : (-(d : E)) = algebraMap ℚ E (-(d : ℚ))` using `by simp`.

Rewrite using `[h]`. Conclude with `isIntegral_algebraMap`. Establish `hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E)`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Conclude with `hx`.

Use `clear hx`. Proceed by induction on `hx' using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Conclude with `⟨0, 1, by simp [hy]⟩`.

Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨a, b, rfl⟩` from `hy`. Take `⟨c, e, rfl⟩` from `hz`. Conclude with `⟨a + c, b + e, by push_cast; ring⟩`.

Consider the case `mul y z _ _ hy hz`. Take `⟨a, b, rfl⟩` from `hy`. Take `⟨c, e, rfl⟩` from `hz`. Use `⟨a * c - d * b * e, a * e + b * c, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Take the linear combination `(b : E) * (e : E) * hs`.
-/
theorem UpperTheory.adjoin_sqrt_eq_rat_span :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), s ^ 2 = -(d : E) → ∀ x : E, x ∈ IntermediateField.adjoin ℚ ({s} : Set E) → ∃ a b : ℚ, x = (a : E) + (b : E) * s := by
  intro E _ _ d s hs x hx
  have hint : IsIntegral ℚ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hs]
    have h : (-(d : E)) = algebraMap ℚ E (-(d : ℚ)) := by simp
    rw [h]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin ℚ ({s} : Set E) := by
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
    obtain ⟨c, e, rfl⟩ := hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, e, rfl⟩ := hz
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : E) * (e : E) * hs
