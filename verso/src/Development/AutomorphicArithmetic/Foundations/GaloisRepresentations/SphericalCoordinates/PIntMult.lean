import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

namespace UpperTheory.Gal.W2

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem intMult_of : IntMult := by
  unfold IntMult
  intro O _ bar D' ga r hr h
  let Iv : Ideal ℤ := Ideal.span {x | ∃ u u', D'.EF u u' = x}
  have hval : ∀ u u', D'.EF u u' ∈ Iv := fun u u' => Ideal.subset_span ⟨u, u', rfl⟩
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal Iv).principal
  have hc' : Iv = Ideal.span {c} := hc
  have key : ∀ x ∈ Iv, ∃ y ∈ Iv, (y : ℚ) = r * x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, u', rfl⟩ := hx
      exact ⟨_, hval (ga u) (ga u'), h u u'⟩
    | zero => exact ⟨0, Iv.zero_mem, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨y, hy, e⟩ := iha
      obtain ⟨z, hz, e'⟩ := ihb
      exact ⟨y + z, Iv.add_mem hy hz, by push_cast; rw [e, e']; ring⟩
    | smul a x _ ih =>
      obtain ⟨y, hy, e⟩ := ih
      exact ⟨a * y, Iv.mul_mem_left a hy, by simp only [smul_eq_mul]; push_cast; rw [e]; ring⟩
  by_cases hc0 : c = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have hz : ∀ u u', D'.EF u u' = 0 := fun u u' => by
      have := hval u u'
      rw [hc', hc0, Ideal.mem_span_singleton] at this
      simpa using this
    rw [hz, hz, mul_zero]
  · have hcI : c ∈ Iv := by rw [hc']; exact Ideal.mem_span_singleton_self c
    obtain ⟨y, hy, e⟩ := key c hcI
    rw [hc', Ideal.mem_span_singleton] at hy
    obtain ⟨m, rfl⟩ := hy
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hm : (m : ℚ) = r := by
      push_cast at e
      have : (c : ℚ) * m = c * r := by rw [e]; ring
      exact mul_left_cancel₀ hcq this
    refine ⟨m, ?_, fun u u' => ?_⟩
    · have : (0 : ℚ) < m := hm ▸ hr
      exact_mod_cast this
    · have := h u u'
      rw [← hm] at this
      exact_mod_cast this

end UpperTheory.Gal.W2
