import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨z, rfl⟩` from `hζ`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, AlgEquiv.mul_apply, hσ, map_mul, AlgEquiv.commutes, ih]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pow_apply_eq_pow_mul_of_apply_eq_mul {F Ω : Type} [Field F] [Field Ω]
    [Algebra F Ω] (σ : Ω ≃ₐ[F] Ω) (ρ ζ : Ω) (hζ : ζ ∈ Set.range (algebraMap F Ω))
    (hσ : σ ρ = ζ * ρ) (k : ℕ) : (σ ^ k) ρ = ζ ^ k * ρ := by
  obtain ⟨z, rfl⟩ := hζ
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgEquiv.mul_apply, hσ, map_mul, AlgEquiv.commutes, ih]
    ring

/- English proof (translation)
Establish `hk : ∀ k, (σ ^ k) (ρ ^ i) = (ζ ^ i) ^ k * ρ ^ i`. Introduce `k`. Rewrite using `[map_pow, pow_apply_eq_pow_mul_of_apply_eq_mul σ ρ ζ hζF hσ k]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hk, ← Finset.sum_mul]`.

Distinguish the cases in `h1 : ζ ^ i = 1`. Rewrite using `[h1]`. Simplify using `only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Take `⟨m, rfl⟩` from `(hζ.pow_eq_one_iff_dvd i).1 h1`. Rewrite using `[pow_mul, hρ, ← map_pow, ← map_natCast (algebraMap F Ω) n, ← map_mul]`.

Conclude with `Subalgebra.algebraMap_mem _ _`. Rewrite using `[geom_sum_eq h1, ← pow_mul, mul_comm i n, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div, zero_mul]`. Conclude with `Subalgebra.zero_mem _`.
-/
private theorem sum_pow_apply_pow_mem_bot_of_kummer {F Ω : Type} [Field F] [Field Ω]
    [Algebra F Ω] (n : ℕ) (σ : Ω ≃ₐ[F] Ω) (ρ ζ : Ω) (c : F) (hρ : ρ ^ n = algebraMap F Ω c)
    (hζ : IsPrimitiveRoot ζ n) (hζF : ζ ∈ Set.range (algebraMap F Ω)) (hσ : σ ρ = ζ * ρ)
    (i : ℕ) : ∑ k ∈ Finset.range n, (σ ^ k) (ρ ^ i) ∈ (⊥ : Subalgebra F Ω) := by
  have hk : ∀ k, (σ ^ k) (ρ ^ i) = (ζ ^ i) ^ k * ρ ^ i := by
    intro k
    rw [map_pow, pow_apply_eq_pow_mul_of_apply_eq_mul σ ρ ζ hζF hσ k]
    ring
  simp_rw [hk, ← Finset.sum_mul]
  by_cases h1 : ζ ^ i = 1
  · rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    obtain ⟨m, rfl⟩ := (hζ.pow_eq_one_iff_dvd i).1 h1
    rw [pow_mul, hρ, ← map_pow, ← map_natCast (algebraMap F Ω) n, ← map_mul]
    exact Subalgebra.algebraMap_mem _ _
  · rw [geom_sum_eq h1, ← pow_mul, mul_comm i n, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div, zero_mul]
    exact Subalgebra.zero_mem _

/- English proof (translation)
Introduce `F Ω _ _ _ _ n q ρ ζ c σ φ hn hρ hφc hφF hroots hζ hσ hφζ x hx`. Establish `hζF : ζ ∈ Set.range (algebraMap F Ω)` using `hroots ζ hζ.pow_eq_one`. Use `⟨?_, fun hsx => ?_⟩` and prove the remaining obligations. Establish `hρ' : φ (σ ρ) = (σ ^ q) (φ ρ)`. Distinguish the cases in `h0 : ρ = 0`.

Simplify using `[h0]`. Establish `hc : algebraMap F Ω c ≠ 0` using `by rw [← hρ]; exact pow_ne_zero _ h0`. Establish `hξ : (φ ρ / ρ) ^ n = 1`. Rewrite using `[div_pow, ← map_pow, hρ, hφc, div_self hc]`. Take `⟨e, he⟩` from `hroots _ hξ`.

Establish `hφρ : φ ρ = algebraMap F Ω e * ρ` using `by rw [he, div_mul_cancel₀ _ h0]`. Rewrite using `[hσ, map_mul, hφζ, hφρ, map_mul, AlgEquiv.commutes, pow_apply_eq_pow_mul_of_apply_eq_mul σ ρ ζ hζF hσ q]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem y hy => rw [Set.mem_singleton_iff.1 hy]`.

Conclude with `hρ'`. Consider the case `algebraMap a`. Take `⟨b, hb⟩` from `hφF a`. Rewrite using `[AlgEquiv.commutes, ← hb]`. Conclude with `((σ ^ q).commutes b).symm`.

Consider the case `add y z _ _ hy hz => simp only [map_add, hy, hz]`. Consider the case `inv y _ hy => simp only [map_inv₀, hy]`. Consider the case `mul y z _ _ hy hz => simp only [map_mul, hy, hz]`. Establish `halg : IsAlgebraic F ρ` using `⟨Polynomial.X ^ n - Polynomial.C c, (Polynomial.monic_X_pow_sub_C c hn.ne').ne_zero, by simp [hρ]⟩`. Establish `hx' : x ∈ Algebra.adjoin F {ρ}`.

Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]`. Conclude with `(IntermediateField.mem_toSubalgebra _ _).2 hx`. Establish `havg : ∀ y ∈ Algebra.adjoin F {ρ}, ∑ k ∈ Finset.range n, (σ ^ k) y ∈ (⊥ : Subalgebra F Ω)`. Introduce `y hy`. Rewrite `hy` using `[Algebra.adjoin_singleton_eq_range_aeval]`.

Take `⟨p, rfl⟩` from `(AlgHom.mem_range _).1 hy`. Rewrite using `[Polynomial.aeval_eq_sum_range]`. Repeatedly rewrite using `[map_sum, map_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Subalgebra.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.smul_sum]`. Conclude with `Subalgebra.smul_mem _ (sum_pow_apply_pow_mem_bot_of_kummer n σ ρ ζ c hρ hζ hζF hσ i) _`. Establish `hall : ∀ k : ℕ, (σ ^ k) x = x`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hsx, ih]`. Establish `hsum` using `havg x hx'`. Rewrite `hsum` using `[hall, Finset.sum_const, Finset.card_range]`. Take `⟨b, hb⟩` from `Algebra.mem_bot.1 hsum`.

Establish `hn0 : (n : F) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Establish `hn0' : (n : Ω) ≠ 0`. Rewrite using `[← map_natCast (algebraMap F Ω) n]`. Conclude with `(map_ne_zero _).2 hn0`. Use `⟨b / n, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, hb, map_natCast, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem kummer_twist_relation_and_fixed_field :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n q : ℕ) (ρ ζ : Ω) (c : F) (σ : Ω ≃ₐ[F] Ω) (φ : Ω →+* Ω), 0 < n → ρ ^ n = algebraMap F Ω c → φ (algebraMap F Ω c) = algebraMap F Ω c → (∀ a : F, φ (algebraMap F Ω a) ∈ Set.range (algebraMap F Ω)) → (∀ ξ : Ω, ξ ^ n = 1 → ξ ∈ Set.range (algebraMap F Ω)) → IsPrimitiveRoot ζ n → σ ρ = ζ * ρ → φ ζ = ζ ^ q → ∀ x ∈ IntermediateField.adjoin F ({ρ} : Set Ω), φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ Set.range (algebraMap F Ω)) := by
  intro F Ω _ _ _ _ n q ρ ζ c σ φ hn hρ hφc hφF hroots hζ hσ hφζ x hx
  have hζF : ζ ∈ Set.range (algebraMap F Ω) := hroots ζ hζ.pow_eq_one
  refine ⟨?_, fun hsx => ?_⟩
  ·
    have hρ' : φ (σ ρ) = (σ ^ q) (φ ρ) := by
      by_cases h0 : ρ = 0
      · simp [h0]
      · have hc : algebraMap F Ω c ≠ 0 := by rw [← hρ]; exact pow_ne_zero _ h0

        have hξ : (φ ρ / ρ) ^ n = 1 := by
          rw [div_pow, ← map_pow, hρ, hφc, div_self hc]
        obtain ⟨e, he⟩ := hroots _ hξ
        have hφρ : φ ρ = algebraMap F Ω e * ρ := by rw [he, div_mul_cancel₀ _ h0]
        rw [hσ, map_mul, hφζ, hφρ, map_mul, AlgEquiv.commutes,
          pow_apply_eq_pow_mul_of_apply_eq_mul σ ρ ζ hζF hσ q]
        ring
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hρ'
    | algebraMap a =>
      obtain ⟨b, hb⟩ := hφF a
      rw [AlgEquiv.commutes, ← hb]
      exact ((σ ^ q).commutes b).symm
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | inv y _ hy => simp only [map_inv₀, hy]
    | mul y z _ _ hy hz => simp only [map_mul, hy, hz]
  ·
    have halg : IsAlgebraic F ρ :=
      ⟨Polynomial.X ^ n - Polynomial.C c, (Polynomial.monic_X_pow_sub_C c hn.ne').ne_zero,
        by simp [hρ]⟩
    have hx' : x ∈ Algebra.adjoin F {ρ} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
      exact (IntermediateField.mem_toSubalgebra _ _).2 hx
    have havg : ∀ y ∈ Algebra.adjoin F {ρ},
        ∑ k ∈ Finset.range n, (σ ^ k) y ∈ (⊥ : Subalgebra F Ω) := by
      intro y hy
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
      rw [Polynomial.aeval_eq_sum_range]
      simp_rw [map_sum, map_smul]
      rw [Finset.sum_comm]
      refine Subalgebra.sum_mem _ fun i _ => ?_
      rw [← Finset.smul_sum]
      exact Subalgebra.smul_mem _
        (sum_pow_apply_pow_mem_bot_of_kummer n σ ρ ζ c hρ hζ hζF hσ i) _
    have hall : ∀ k : ℕ, (σ ^ k) x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hsx, ih]
    have hsum := havg x hx'
    simp_rw [hall, Finset.sum_const, Finset.card_range] at hsum
    obtain ⟨b, hb⟩ := Algebra.mem_bot.1 hsum
    have hn0 : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hn0' : (n : Ω) ≠ 0 := by
      rw [← map_natCast (algebraMap F Ω) n]; exact (map_ne_zero _).2 hn0
    refine ⟨b / n, ?_⟩
    rw [map_div₀, hb, map_natCast, nsmul_eq_mul]
    field_simp

end GlobalTheory
