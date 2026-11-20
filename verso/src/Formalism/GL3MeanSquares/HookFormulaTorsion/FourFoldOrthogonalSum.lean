import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

/- English proof (translation)
Introduce `K _ _ x hx`. Establish `hx' : (x : K) ≠ 0` using `by exact_mod_cast hx`. Establish `hne : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≠ 0` using `fun φ => by`. Rewrite using `[norm_ne_zero_iff]`. Conclude with `(map_ne_zero φ).mpr hx'`.

Rewrite using `[← Real.log_prod (fun φ _ => hne φ)]`. Apply `Real.log_nonneg` to reduce the goal to its premises. Rewrite using `[← norm_prod]`. Establish `key : (∏ φ : K →+* ℂ, φ (x : K)) = algebraMap ℚ ℂ (Algebra.norm ℚ (x : K))`. Rewrite using `[Algebra.norm_eq_prod_embeddings ℚ ℂ]`.

Conclude with `Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)`. Rewrite using `[key, ← Algebra.coe_norm_int x]`. Establish `hN0 : Algebra.norm ℤ x ≠ 0`. Introduce `h0`. Establish `h5 : Algebra.norm ℚ (x : K) ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hx'`.

Apply `h5` to reduce the goal to its premises. Rewrite using `[← Algebra.coe_norm_int x, h0, Int.cast_zero]`. Rewrite using `[eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]`. Conclude with `Int.one_le_abs hN0` after adjusting the coercions.
-/
theorem integer_mean_log_bound : IntegerMeanLog := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hne : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≠ 0 := fun φ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero φ).mpr hx'
  rw [← Real.log_prod (fun φ _ => hne φ)]
  apply Real.log_nonneg
  rw [← norm_prod]
  have key : (∏ φ : K →+* ℂ, φ (x : K)) = algebraMap ℚ ℂ (Algebra.norm ℚ (x : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [key, ← Algebra.coe_norm_int x]
  have hN0 : Algebra.norm ℤ x ≠ 0 := by
    intro h0
    have h5 : Algebra.norm ℚ (x : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx'
    apply h5
    rw [← Algebra.coe_norm_int x, h0, Int.cast_zero]
  rw [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hN0

/- English proof (translation)
Introduce `x j s hs hj hx`. Apply the tactic sequence `have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Set `R` to `integralClosure ℤ ℂ`. Set `jR : R` to `⟨j, hj⟩`.

Set `q : Polynomial R` to `(Polynomial.X - Polynomial.C (s : R)) ^ 3 - Polynomial.C jR * Polynomial.X`. Establish `hq : q.Monic`. Apply `Polynomial.Monic.sub_of_left ((Polynomial.monic_X_sub_C _).pow 3)` to reduce the goal to its premises. Rewrite using `[Polynomial.degree_pow, Polynomial.degree_X_sub_C]`. Use `lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_` and prove the remaining obligations.

Evaluate the numerical expressions. Establish `hxR : IsIntegral R x`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations. Simplify using `only [q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_mul]`. Simplify using `only [map_intCast]`.

Establish `hjR : algebraMap R ℂ jR = j` using `rfl`. Rewrite using `[hjR]`. Take the linear combination `hx`. Conclude with `isIntegral_trans x hxR`. Introduce `h`.

Rewrite `hx` using `[h]`. Apply `hs0` to reduce the goal to its premises. Establish `h3 : (s : ℂ) ^ 3 = 0` using `by linear_combination -hx`. Conclude with `(pow_eq_zero_iff (by norm_num)).mp h3`.
-/
theorem weber_function_root : WeberRoot := by
  intro x j s hs hj hx
  have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · let R := integralClosure ℤ ℂ
    let jR : R := ⟨j, hj⟩
    let q : Polynomial R := (Polynomial.X - Polynomial.C (s : R)) ^ 3 - Polynomial.C jR * Polynomial.X
    have hq : q.Monic := by
      apply Polynomial.Monic.sub_of_left ((Polynomial.monic_X_sub_C _).pow 3)
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_
      norm_num
    have hxR : IsIntegral R x := by
      refine ⟨q, hq, ?_⟩
      simp only [q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_mul]
      simp only [map_intCast]
      have hjR : algebraMap R ℂ jR = j := rfl
      rw [hjR]
      linear_combination hx
    exact isIntegral_trans x hxR
  · intro h
    rw [h] at hx
    apply hs0
    have h3 : (s : ℂ) ^ 3 = 0 := by linear_combination -hx
    exact (pow_eq_zero_iff (by norm_num)).mp h3

end Formalism.HermitianLattices.IntegralLatticeDensity
