import Mathlib

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Proceed by induction.

Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
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
