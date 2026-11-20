import Mathlib

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.TwoRealCharacters

/- English proof (translation)
Establish `hs : 1 < (σ : ℂ).re` using `by simpa using hσ`. Establish `h` using `(LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum`. Rewrite `h` using `[LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs, ← LFunction_eq_LSeries χ hs]`. Establish `h'` using `Complex.hasSum_re h`. Use `h' using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `n`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]`. Simplify using `[Pi.mul_apply, Complex.div_ofReal_re, mul_div_assoc]`.

Rewrite using `[neg_div, Complex.neg_re]`.
-/
theorem hasSum_re_neg_logDeriv (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (χ n).re * (vonMangoldt n / (n : ℝ) ^ σ))
      (-(deriv (LFunction χ) σ / LFunction χ σ).re) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have h := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs] at h
  have h' := Complex.hasSum_re h
  convert h' using 1
  · funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast n,
        ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp [Pi.mul_apply, Complex.div_ofReal_re, mul_div_assoc]
  · rw [neg_div, Complex.neg_re]

/- English proof (translation)
Distinguish the cases in `ha : IsUnit a`. Establish `hsq : ∀ φ : DirichletCharacter ℂ q, φ ^ 2 = 1 → φ a = 1 ∨ φ a = -1`. Introduce `φ hφ`. Apply `mul_self_eq_one_iff.mp` to reduce the goal to its premises. Establish `hval` using `congrArg (fun ξ : DirichletCharacter ℂ q => ξ a) hφ`.

Simplify using `only [MulChar.pow_apply' φ two_ne_zero, MulChar.one_apply ha] at hval`. Rewrite using `[← pow_two]`. Conclude with `hval`. Rewrite using `[MulChar.one_apply ha, MulChar.coeToFun_mul, Pi.mul_apply]`. Apply the tactic sequence `rcases hsq χ hχ with h1 | h1 <;> rcases hsq ψ hψ with h2 | h2 <;> norm_num [h1, h2]`.

Rewrite using `[MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]`. Simplify using the standard rewrite rules.
-/
theorem re_sum_nonneg (q : ℕ) (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (a : ZMod q) :
    0 ≤ ((1 : DirichletCharacter ℂ q) a).re + (χ a).re + (ψ a).re + ((χ * ψ) a).re := by
  by_cases ha : IsUnit a
  · have hsq : ∀ φ : DirichletCharacter ℂ q, φ ^ 2 = 1 → φ a = 1 ∨ φ a = -1 := by
      intro φ hφ
      apply mul_self_eq_one_iff.mp
      have hval := congrArg (fun ξ : DirichletCharacter ℂ q => ξ a) hφ
      simp only [MulChar.pow_apply' φ two_ne_zero, MulChar.one_apply ha] at hval
      rw [← pow_two]
      exact hval
    rw [MulChar.one_apply ha, MulChar.coeToFun_mul, Pi.mul_apply]
    rcases hsq χ hχ with h1 | h1 <;> rcases hsq ψ hψ with h2 | h2 <;> norm_num [h1, h2]
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha,
      MulChar.map_nonunit _ ha]
    simp

/- English proof (translation)
Introduce `q _ χ ψ σ hχ hψ hσ`. Establish `h` using `(((hasSum_re_neg_logDeriv q 1 σ hσ).add (hasSum_re_neg_logDeriv q χ σ hσ)).add (hasSum_re_neg_logDeriv q ψ σ hσ)).add (hasSum_re_neg_logDeriv q (χ * ψ) σ hσ)`. Establish `hnn` using `h.nonneg fun n => by`. Establish `h1` using `re_sum_nonneg q χ ψ hχ hψ (n : ZMod q)`. Establish `h2 : 0 ≤ vonMangoldt n / (n : ℝ) ^ σ` using `div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)`.

Establish `h3` using `mul_nonneg h1 h2`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem neg_sum_logDeriv_nonneg : ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q) (σ : ℝ), χ ^ 2 = 1 → ψ ^ 2 = 1 → 1 < σ → 0 ≤ -((deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + (deriv (LFunction χ) σ / LFunction χ σ).re + (deriv (LFunction ψ) σ / LFunction ψ σ).re + (deriv (LFunction (χ * ψ)) σ / LFunction (χ * ψ) σ).re) := by
  intro q _ χ ψ σ hχ hψ hσ
  have h := (((hasSum_re_neg_logDeriv q 1 σ hσ).add (hasSum_re_neg_logDeriv q χ σ hσ)).add
    (hasSum_re_neg_logDeriv q ψ σ hσ)).add (hasSum_re_neg_logDeriv q (χ * ψ) σ hσ)
  have hnn := h.nonneg fun n => by
    have h1 := re_sum_nonneg q χ ψ hχ hψ (n : ZMod q)
    have h2 : 0 ≤ vonMangoldt n / (n : ℝ) ^ σ :=
      div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    have h3 := mul_nonneg h1 h2
    linarith
  linarith

end GlobalTheory.TwoRealCharacters
