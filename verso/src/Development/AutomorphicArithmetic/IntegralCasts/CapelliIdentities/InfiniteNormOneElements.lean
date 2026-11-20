import Mathlib

/- English proof (translation)
Introduce `F E _ _ _ _ σ hE hσ`. Take `⟨w⟩ : Nonempty (NumberField.InfinitePlace E)` from `inferInstance`. Establish `hw : ¬ NumberField.ComplexEmbedding.IsReal w.embedding` using `NumberField.InfinitePlace.isComplex_iff.mp (hE.isComplex w)`. Generalize the expression as in `w.embedding = τ at hw`. Establish `hinv : ∀ x : E, σ (σ x) = x` using `fun x => τ.injective (by rw [hσ, hσ, star_star])`.

Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hw` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Use `hσ τ x` as an intermediate fact. Rewrite `this` using `[h]`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Conclude with `this.symm`.

Establish `h1 : ∀ n : ℕ, (n : E) + a ≠ 0`. Introduce `n hn`. Apply `ha` to reduce the goal to its premises. Establish `: a = -(n : E)` using `by linear_combination hn`. Rewrite using `[this, map_neg, map_natCast]`.

Establish `h2 : ∀ n : ℕ, (n : E) + σ a ≠ 0`. Introduce `n hn`. Apply `h1 n` to reduce the goal to its premises. Use `congrArg σ hn` as an intermediate fact. Rewrite `this` using `[map_add, map_natCast, hinv, map_zero]`. Then use the resulting hypothesis.

Use `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : E) + a) / ((n : E) + σ a)) ?_ ?_` and prove the remaining obligations. Introduce `m n hmn`. Establish `h3` using `(div_eq_div_iff (h2 m) (h2 n)).mp hmn`. Establish `h4 : ((m : E) - n) * (σ a - a) = 0` using `by linear_combination h3`. Break down `mul_eq_zero.mp h4 with h | h` into its components or cases.

Conclude with `Nat.cast_injective (R := E) (sub_eq_zero.mp h)`. Conclude with `absurd (sub_eq_zero.mp h) ha`. Introduce `n show _ * σ _ = 1`. Rewrite using `[map_div₀, map_add, map_add, map_natCast, hinv, div_mul_div_cancel₀ (h2 n), div_self (h1 n)]`.
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
