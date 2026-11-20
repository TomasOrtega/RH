import Mathlib

namespace GlobalTheory.NonzeroMultipleInSpan

open NumberField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_ne_zero_smul_mem_span {LL : Type} [Field LL] [NumberField LL] {n : ℕ}
    (T : Set (Fin n → LL)) :
    ∀ x ∈ Submodule.span LL T, ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm b a]
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ b hay) (Submodule.smul_mem _ a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 LL)) c
    refine ⟨(q : 𝓞 LL) * a, mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩
    have h : ((q : 𝓞 LL) * a) • (c • y) = p • (a • y) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      simp only at hpq
      rw [← hpq]
      ring
    rw [h]
    exact Submodule.smul_mem _ p hay

end GlobalTheory.NonzeroMultipleInSpan
