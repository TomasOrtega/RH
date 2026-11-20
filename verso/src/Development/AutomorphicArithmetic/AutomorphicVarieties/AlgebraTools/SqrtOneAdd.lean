import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Evaluate the numerical expressions. Extract witnesses or component facts from the available result.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Evaluate the numerical expressions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.sqrt_one_add :
    ∀ {B : Type} [CommRing B] (I : Ideal B) [HenselianRing B I] (a : B), IsUnit (2 : B) → a - 1 ∈ I → ∃ α : Bˣ, (α : B) ^ 2 = a ∧ (α : B) - 1 ∈ I := by
  intro B _ I _ a h2 ha
  have hmon : (X ^ 2 - C a : B[X]).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    norm_num
  obtain ⟨α, hroot, hα⟩ := HenselianRing.is_henselian (X ^ 2 - C a) hmon 1
    (by
      have : (X ^ 2 - C a : B[X]).eval 1 = -(a - 1) := by simp <;> ring
      rw [this]
      exact I.neg_mem ha)
    (by
      have : (derivative (X ^ 2 - C a : B[X])).eval 1 = 2 := by
        simp only [derivative_sub, derivative_X_pow, derivative_C, eval_sub, eval_mul, eval_C,
          eval_pow, eval_one, eval_zero]
        norm_num
      rw [this]
      exact h2.map _)
  have hu : IsUnit α := by
    have hj := HenselianRing.jac (I := I) hα
    rw [Ideal.mem_jacobson_bot] at hj
    have := hj 1
    simpa using this
  refine ⟨hu.unit, ?_, ?_⟩
  · simp only [IsUnit.unit_spec]
    have := hroot
    simp [Polynomial.IsRoot] at this
    exact sub_eq_zero.mp this
  · simpa using hα
