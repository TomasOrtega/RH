import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
The claim follows from `|((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ x‖ := by have h : ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ x := by rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x) (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x] simp rw [← norm_ …`.
-/
theorem abs_norm_eq_prod_embeddings_closeOne {E : Type} [Field E] [NumberField E] (x : E) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ x‖ := by
  have h : ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ x := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x)
      (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    simp
  rw [← norm_prod, ← h, Complex.norm_ratCast]

/- English proof (translation)
Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E ε hint`. Assume the negation of the conclusion as `hne`. Establish `hxE : algebraMap (𝓞 E) E (r - 1) = ε - 1` using `by simp [hr]`. Establish `hx0 : r - 1 ≠ 0`. Introduce `h`.

Rewrite `hxE` using `[h, map_zero]`. Conclude with `hne (sub_eq_zero.mp hxE.symm)`. Establish `hmem : r - 1 ∈ w.asIdeal ^ K`. Rewrite using `[← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]`. Use `hw using 2` and compare the differences between its conclusion and the goal.

Establish `hdvd : w.asIdeal ^ K ∣ Ideal.span {r - 1}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hmem`. Establish `hN` using `map_dvd Ideal.absNorm hdvd`. Rewrite `hN` using `[map_pow, Ideal.absNorm_span_singleton]`.

Establish `hnz : (Algebra.norm ℤ (r - 1)).natAbs ≠ 0`. Rewrite using `[← Ideal.absNorm_span_singleton, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hx0`. Establish `hle` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hnz) hN`. Establish `h2 : 2 ≤ Ideal.absNorm w.asIdeal`.

Establish `h0 : Ideal.absNorm w.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `w.ne_bot`. Establish `h1 : Ideal.absNorm w.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `w.isPrime.ne_top`. Use linear arithmetic over natural numbers and integers. Establish `hlow : 2 ^ K ≤ (Algebra.norm ℤ (r - 1)).natAbs` using `le_trans (Nat.pow_le_pow_left h2 K) hle`. Establish `hup : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) ≤ 2 ^ Module.finrank ℚ E`. Establish `h1 : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) = |((Algebra.norm ℚ (ε - 1) : ℚ) : ℝ)|`.

Rewrite using `[← hxE, ← Algebra.coe_norm_int (r - 1), Nat.cast_natAbs]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h1, abs_norm_eq_prod_embeddings_closeOne]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun φ _ => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, map_one]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = 2 ^ Module.finrank ℚ E := by`. Rewrite using `[Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card]`.

Establish `hlowR : (2 : ℝ) ^ K ≤ 2 ^ Module.finrank ℚ E`. Establish `: ((2 ^ K : ℕ) : ℝ) ≤ ((Algebra.norm ℤ (r - 1)).natAbs : ℝ)` using `by exact_mod_cast hlow`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlowR` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem eq_one_of_norm_one_of_valuation_sub_one_le (E : Type) [Field E] [NumberField E] (ε : E)
    (w : HeightOneSpectrum (𝓞 E)) (K : ℕ) (hK : Module.finrank ℚ E < K)
    (hint : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ε ≤ 1)
    (habs : ∀ φ : E →+* ℂ, ‖φ ε‖ = 1)
    (hw : w.valuation E (ε - 1) ≤ WithZero.exp (-(K : ℤ))) : ε = 1 := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E ε hint
  by_contra hne
  have hxE : algebraMap (𝓞 E) E (r - 1) = ε - 1 := by simp [hr]
  have hx0 : r - 1 ≠ 0 := by
    intro h
    rw [h, map_zero] at hxE
    exact hne (sub_eq_zero.mp hxE.symm)
  have hmem : r - 1 ∈ w.asIdeal ^ K := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    convert hw using 2
  have hdvd : w.asIdeal ^ K ∣ Ideal.span {r - 1} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hN := map_dvd Ideal.absNorm hdvd
  rw [map_pow, Ideal.absNorm_span_singleton] at hN
  have hnz : (Algebra.norm ℤ (r - 1)).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hx0
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hnz) hN
  have h2 : 2 ≤ Ideal.absNorm w.asIdeal := by
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    omega
  have hlow : 2 ^ K ≤ (Algebra.norm ℤ (r - 1)).natAbs :=
    le_trans (Nat.pow_le_pow_left h2 K) hle
  have hup : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) ≤ 2 ^ Module.finrank ℚ E := by
    have h1 : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) = |((Algebra.norm ℚ (ε - 1) : ℚ) : ℝ)| := by
      rw [← hxE, ← Algebra.coe_norm_int (r - 1), Nat.cast_natAbs]
      push_cast
      rfl
    rw [h1, abs_norm_eq_prod_embeddings_closeOne]
    calc ∏ φ : E →+* ℂ, ‖φ (ε - 1)‖ ≤ ∏ _φ : E →+* ℂ, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun φ _ => ?_)
          rw [map_sub, map_one]
          calc ‖φ ε - 1‖ ≤ ‖φ ε‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [habs φ, norm_one]; norm_num
      _ = 2 ^ Module.finrank ℚ E := by
          rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card]
  have hlowR : (2 : ℝ) ^ K ≤ 2 ^ Module.finrank ℚ E := by
    have : ((2 ^ K : ℕ) : ℝ) ≤ ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) := by exact_mod_cast hlow
    push_cast at this
    linarith
  have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlowR
  omega

end GlobalTheory
