import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qh30.artin :
    ∀ {P : Type} [inst : Mul P] (T : Finset (P → ℂ))
    (c : (P → ℂ) → ℂ),
    (∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q) →
      (∀ (p : P), ∑ χ ∈ T, c χ * χ p = (0 : ℂ)) → ∀ χ ∈ T, c χ = (0 : ℂ) := by
  intro P inst T
  classical
  induction T using Finset.induction_on with
  | empty => intro c _ _ χ hχ; simp at hχ
  | insert ψ T hψ ih =>
    intro c hT h
    have hψm := hT ψ (Finset.mem_insert_self ψ T)
    have hT' : ∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q :=
      fun χ hχ => hT χ (Finset.mem_insert_of_mem hχ)
    have key : ∀ q : P, ∀ χ ∈ T, c χ * (χ q - ψ q) = 0 := by
      intro q
      refine ih (fun χ => c χ * (χ q - ψ q)) hT' ?_
      intro p
      have h1 := h (q * p)
      have h2 := h p
      rw [Finset.sum_insert hψ] at h1 h2
      have h3 : ∑ χ ∈ T, c χ * (χ q - ψ q) * χ p
          = ∑ χ ∈ T, c χ * χ (q * p) - ψ q * ∑ χ ∈ T, c χ * χ p := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [(hT' χ hχ).2]
        ring
      rw [hψm.2] at h1
      rw [h3]
      linear_combination h1 - ψ q * h2
    have hc : ∀ χ ∈ T, c χ = 0 := by
      intro χ hχ
      by_contra hne
      have : χ = ψ := by
        funext q
        exact sub_eq_zero.mp ((mul_eq_zero.mp (key q χ hχ)).resolve_left hne)
      exact hψ (this ▸ hχ)
    have hcψ : c ψ = 0 := by
      by_contra hne
      apply hψm.1
      funext p
      have h2 := h p
      rw [Finset.sum_insert hψ, Finset.sum_eq_zero (fun χ hχ => by rw [hc χ hχ, zero_mul]),
        add_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_left hne
    intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hcψ
    · exact hc χ hχ
