import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Introduce `B _ I _ a h2 ha`. Establish `hmon : (X ^ 2 - C a : B[X]).Monic`. Apply `Polynomial.monic_X_pow_sub_C` to reduce the goal to its premises. Evaluate the numerical expressions. Take `⟨α, hroot, hα⟩` from `HenselianRing.is_henselian (X ^ 2 - C a) hmon 1 (by`.

Apply the tactic sequence `have : (X ^ 2 - C a : B[X]).eval 1 = -(a - 1) := by simp <;> ring`. Rewrite using `[this]`. Conclude with `I.neg_mem ha)`. Use the proof step `(by`. Establish `: (derivative (X ^ 2 - C a : B[X])).eval 1 = 2`.

Simplify using `only [derivative_sub, derivative_X_pow, derivative_C, eval_sub, eval_mul, eval_C, eval_pow, eval_one, eval_zero]`. Evaluate the numerical expressions. Rewrite using `[this]`. Conclude with `h2.map _)`. Establish `hu : IsUnit α`.

Establish `hj` using `HenselianRing.jac (I := I) hα`. Rewrite `hj` using `[Ideal.mem_jacobson_bot]`. Use `hj 1` as an intermediate fact. Simplify using `using this`. Use `⟨hu.unit, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [IsUnit.unit_spec]`. Use `hroot` as an intermediate fact. Simplify using `[Polynomial.IsRoot] at this`. Conclude with `sub_eq_zero.mp this`. Simplify using `using hα`.
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
