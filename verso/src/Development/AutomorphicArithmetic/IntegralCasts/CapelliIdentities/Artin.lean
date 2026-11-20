import Mathlib

/- English proof (translation)
Introduce `P inst T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro c _ _ χ hχ`. Simplify using `at hχ`. Consider the case `insert ψ T hψ ih`.

Introduce `c hT h`. Establish `hψm` using `hT ψ (Finset.mem_insert_self ψ T)`. Establish `hT' : ∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q` using `fun χ hχ => hT χ (Finset.mem_insert_of_mem hχ)`. Establish `key : ∀ q : P, ∀ χ ∈ T, c χ * (χ q - ψ q) = 0`. Introduce `q`.

Use `ih (fun χ => c χ * (χ q - ψ q)) hT' ?_` and prove the remaining obligations. Introduce `p`. Establish `h1` using `h (q * p)`. Establish `h2` using `h p`. Rewrite `h1`, `h2` using `[Finset.sum_insert hψ]`.

Establish `h3 : ∑ χ ∈ T, c χ * (χ q - ψ q) * χ p = ∑ χ ∈ T, c χ * χ (q * p) - ψ q * ∑ χ ∈ T, c χ * χ p`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun χ hχ => ?_` and prove the remaining obligations. Rewrite using `[(hT' χ hχ).2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[hψm.2]`. Rewrite using `[h3]`. Take the linear combination `h1 - ψ q * h2`. Establish `hc : ∀ χ ∈ T, c χ = 0`. Introduce `χ hχ`.

Assume the negation of the conclusion as `hne`. Establish `: χ = ψ`. Use function extensionality and compare the values at `q`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp (key q χ hχ)).resolve_left hne)`. Conclude with `hψ (this ▸ hχ)`.

Establish `hcψ : c ψ = 0`. Assume the negation of the conclusion as `hne`. Apply `hψm.1` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Establish `h2` using `h p`.

Rewrite `h2` using `[Finset.sum_insert hψ, Finset.sum_eq_zero (fun χ hχ => by rw [hc χ hχ, zero_mul]), add_zero]`. Conclude with `(mul_eq_zero.mp h2).resolve_left hne`. Introduce `χ hχ`. Break down `Finset.mem_insert.mp hχ with rfl | hχ` into its components or cases. Conclude with `hcψ`.

Conclude with `hc χ hχ`.
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
