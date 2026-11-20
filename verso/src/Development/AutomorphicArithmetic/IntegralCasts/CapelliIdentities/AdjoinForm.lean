import Mathlib

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

/- English proof (translation)
Introduce `E _ _ d _ x hx y hy`. Establish `hint : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral x`. Establish `h : y ∈ (ℚ⟮x⟯).toSubalgebra` using `hy`. Rewrite `h` using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Use `clear hy`.

Proceed by induction on `h using Algebra.adjoin_induction with`. Consider the case `mem a ha`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Conclude with `⟨0, 1, by simp [ha]⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`.

Consider the case `add a b _ _ iha ihb`. Take `⟨s, t, rfl⟩` from `iha`. Take `⟨s', t', rfl⟩` from `ihb`. Conclude with `⟨s + s', t + t', by push_cast; ring⟩`. Consider the case `mul a b _ _ iha ihb`.

Take `⟨s, t, rfl⟩` from `iha`. Take `⟨s', t', rfl⟩` from `ihb`. Conclude with `⟨s * s' - t * t' * d, s * t' + t * s', by push_cast; linear_combination (t * t' : E) * hx⟩`.
-/
theorem UpperTheory.Reformulated.B.AdjoinForm.adjoin_form :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    {d : ℕ},
    (0 : ℕ) < d → ∀ {x : E}, x ^ (2 : ℕ) = -(↑d : E) → ∀ y ∈ ℚ⟮x⟯, ∃ (s : ℚ) (t : ℚ), y = (↑s : E) + (↑t : E) * x := by
  intro E _ _ d _ x hx y hy
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have h : y ∈ (ℚ⟮x⟯).toSubalgebra := hy
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at h
  clear hy
  induction h using Algebra.adjoin_induction with
  | mem a ha =>
    rw [Set.mem_singleton_iff] at ha
    exact ⟨0, 1, by simp [ha]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ iha ihb =>
    obtain ⟨s, t, rfl⟩ := iha
    obtain ⟨s', t', rfl⟩ := ihb
    exact ⟨s + s', t + t', by push_cast; ring⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨s, t, rfl⟩ := iha
    obtain ⟨s', t', rfl⟩ := ihb
    exact ⟨s * s' - t * t' * d, s * t' + t * s', by push_cast; linear_combination (t * t' : E) * hx⟩
