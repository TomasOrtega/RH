import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.infinite_norm_one_elements :
    ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
        {t : E | t * σ t = 1}.Infinite := by
  intro F E _ _ _ _ σ hE hσ
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hw : ¬ NumberField.ComplexEmbedding.IsReal w.embedding :=
    NumberField.InfinitePlace.isComplex_iff.mp (hE.isComplex w)
  generalize w.embedding = τ at hw
  have hinv : ∀ x : E, σ (σ x) = x := fun x =>
    τ.injective (by rw [hσ, hσ, star_star])
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra h
    push Not at h
    apply hw
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [h] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  have h1 : ∀ n : ℕ, (n : E) + a ≠ 0 := by
    intro n hn
    apply ha
    have : a = -(n : E) := by linear_combination hn
    rw [this, map_neg, map_natCast]
  have h2 : ∀ n : ℕ, (n : E) + σ a ≠ 0 := by
    intro n hn
    apply h1 n
    have := congrArg σ hn
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + a) / ((n : E) + σ a)) ?_ ?_
  · intro m n hmn
    have h3 := (div_eq_div_iff (h2 m) (h2 n)).mp hmn
    have h4 : ((m : E) - n) * (σ a - a) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact Nat.cast_injective (R := E) (sub_eq_zero.mp h)
    · exact absurd (sub_eq_zero.mp h) ha
  · intro n
    show _ * σ _ = 1
    rw [map_div₀, map_add, map_add, map_natCast, hinv, div_mul_div_cancel₀ (h2 n), div_self (h1 n)]
