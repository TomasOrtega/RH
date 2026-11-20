import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qi35.torsSat_mult :
    ∀ {M : Type} [inst : AddCommGroup M] (L : Set M)
    (N : Submodule ℤ M),
    (∀ x ∈ L, ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ n • x ∈ N) → ∀ x ∈ Submodule.span ℤ L, ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ n • x ∈ N := by
  intro M _ L N h x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]
    exact N.smul_mem c hay
