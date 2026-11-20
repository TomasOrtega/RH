import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', LSeries.logMul, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dhPos_iter_logMul (f : ℕ → ℂ) (k n : ℕ) :
    (logMul^[k] f) n = (Complex.log n) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih]
    ring

/- English proof (translation)
Establish `h : abscissaOfAbsConv (↗ψ * ↗Λ) ≤ ((1 : ℝ) : EReal)`. Apply `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable` to reduce the goal to its premises. Introduce `y hy`. Conclude with `DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ (by simp only [Complex.ofReal_re]; exact_mod_cast hy)`. Conclude with `lt_of_le_of_lt h (by exact_mod_cast hs)`.
-/
lemma dhPos_abscissa {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
  have h : abscissaOfAbsConv (↗ψ * ↗Λ) ≤ ((1 : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ (by simp only [Complex.ofReal_re]; exact_mod_cast hy)
  exact lt_of_le_of_lt h (by exact_mod_cast hs)

/- English proof (translation)
Establish `hopen : IsOpen {w : ℂ | 1 < w.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hEq : ∀ z : ℂ, 1 < z.re → negLD ψ z = LSeries (↗ψ * ↗Λ) z`. Introduce `z hz`. Establish `hev : DirichletCharacter.LFunction ψ =ᶠ[nhds z] LSeries (fun n => ψ n)` using `by filter_upwards [hopen.mem_nhds hz] with w hw`. Conclude with `DirichletCharacter.LFunction_eq_LSeries ψ hw`.

Unfold `negLD`. Rewrite using `[hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries ψ hz, DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hz]`. Expand and normalize the polynomial expressions, which then agree. Establish `heq : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ)` using `by filter_upwards [hopen.mem_nhds hs] with z hz`. Conclude with `hEq z hz`.

Rewrite using `[heq.iteratedDeriv_eq, LSeries_iteratedDeriv k (dhPos_abscissa ψ hs), ← mul_assoc, ← mul_pow]`. Evaluate the numerical expressions.
-/
lemma dhPos_iter {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    (-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s = LSeries (logMul^[k] (↗ψ * ↗Λ)) s := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEq : ∀ z : ℂ, 1 < z.re → negLD ψ z = LSeries (↗ψ * ↗Λ) z := by
    intro z hz
    have hev : DirichletCharacter.LFunction ψ =ᶠ[nhds z] LSeries (fun n => ψ n) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    unfold negLD
    rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries ψ hz,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hz]
    ring
  have heq : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hEq z hz
  rw [heq.iteratedDeriv_eq, LSeries_iteratedDeriv k (dhPos_abscissa ψ hs), ← mul_assoc, ← mul_pow]
  norm_num

/- English proof (translation)
Rewrite using `[dhPos_iter ψ k hs]`. Establish `habs : abscissaOfAbsConv (logMul^[k] (↗ψ * ↗Λ)) < s.re`. Establish `e : ∀ j : ℕ, abscissaOfAbsConv (logMul^[j] (↗ψ * ↗Λ)) = abscissaOfAbsConv (↗ψ * ↗Λ)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => rfl`. Consider the case `succ j ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]`. Rewrite using `[e]`. Conclude with `dhPos_abscissa ψ hs`. Establish `hs2` using `(LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum`.

Conclude with `Complex.reCLM.hasSum hs2`.
-/
lemma dhPos_hasSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n ↦ (term (logMul^[k] (↗ψ * ↗Λ)) s n).re)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s).re := by
  rw [dhPos_iter ψ k hs]
  have habs : abscissaOfAbsConv (logMul^[k] (↗ψ * ↗Λ)) < s.re := by
    have e : ∀ j : ℕ, abscissaOfAbsConv (logMul^[j] (↗ψ * ↗Λ)) = abscissaOfAbsConv (↗ψ * ↗Λ) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]
    rw [e]
    exact dhPos_abscissa ψ hs
  have hs2 := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  exact Complex.reCLM.hasSum hs2

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `hn' : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Establish `hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_log (Nat.cast_nonneg n)]`.

Simplify using the standard rewrite rules. Establish `hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg n)]`. Simplify using the standard rewrite rules. Establish `hpos : ((n : ℝ) ^ σ) ≠ 0` using `(Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'`.

Establish `hu : (n : ℂ) ^ ((u : ℂ) * I) ≠ 0` using `Complex.cpow_ne_zero_iff.2 (Or.inl hn')`. Rewrite using `[LSeries.term_of_ne_zero hn, dhPos_iter_logMul, Complex.cpow_add _ _ hn', hpow, hlog]`. Simplify using `only [Pi.mul_apply]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
lemma dhPos_term {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ u : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) ((σ : ℂ) + u * I) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * (ψ n / (n : ℂ) ^ ((u : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    have hu : (n : ℂ) ^ ((u : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn')
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, Complex.cpow_add _ _ hn', hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_log (Nat.cast_nonneg n)]`. Simplify using the standard rewrite rules.

Establish `hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg n)]`. Simplify using the standard rewrite rules. Establish `hpos : ((n : ℝ) ^ σ) ≠ 0` using `(Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'`. Rewrite using `[LSeries.term_of_ne_zero hn, dhPos_iter_logMul, hpow, hlog]`.

Simplify using `only [Pi.mul_apply]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
lemma dhPos_term_real {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) (σ : ℂ) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg n)]
      simp
    have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    have hpos : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
    rw [LSeries.term_of_ne_zero hn, dhPos_iter_logMul, hpow, hlog]
    simp only [Pi.mul_apply]
    push_cast
    field_simp

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[dhPos_term_real, dhPos_term_real, dhPos_term, dhPos_term]`. Simplify using `only [Complex.re_ofReal_mul]`. Establish `hA0 : 0 ≤ (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ)` using `mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))`.

Establish `hz1 : ‖(n : ℂ) ^ ((γ : ℂ) * I)‖ = 1`. Rewrite using `[Complex.norm_natCast_cpow_of_pos hn]`. Simplify using the standard rewrite rules. Establish `hw : -1 ≤ (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re`. Establish `hnorm : ‖χ n / (n : ℂ) ^ ((γ : ℂ) * I)‖ ≤ 1`.

Rewrite using `[norm_div, hz1, div_one]`. Conclude with `DirichletCharacter.norm_le_one χ _`. Establish `h2` using `Complex.abs_re_le_norm (χ n / (n : ℂ) ^ ((γ : ℂ) * I))`. Combine the linear relations using `[(abs_le.1 h2).1]`. Establish `key : 0 ≤ ((1 : DirichletCharacter ℂ q) n).re + (χ₁ n).re + (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re + ((χ * χ₁) n / (n : ℂ) ^ ((γ : ℂ) * I)).re`.

Distinguish the cases in `hu : IsUnit (n : ZMod q)`. Establish `h1n : (1 : DirichletCharacter ℂ q) n = 1` using `MulChar.one_apply hu`. Establish `hsq : χ₁ n * χ₁ n = 1`. Establish `e` using `congrArg (fun ψ : DirichletCharacter ℂ q => ψ n) h1`. Simplify `e` using `only [pow_two, MulChar.mul_apply, MulChar.one_apply hu]`.

Establish `hχ₁ : χ₁ n = 1 ∨ χ₁ n = -1`. Establish `h' : (χ₁ n - 1) * (χ₁ n + 1) = 0` using `by linear_combination hsq`. Break down `mul_eq_zero.1 h' with h | h` into its components or cases. Use `left`. Take the linear combination `h`.

Use `right`. Take the linear combination `h`. Rewrite using `[MulChar.mul_apply, h1n]`. Break down `hχ₁ with h | h` into its components or cases. Rewrite using `[h, mul_one]`.

Simplify using `only [Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h]`. Simplify using `only [Complex.one_re, Complex.neg_re, mul_neg, mul_one, neg_div]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h0 : ∀ ψ : DirichletCharacter ℂ q, ψ n = 0` using `fun ψ => MulChar.map_nonunit ψ hu`. Simplify using `[h0]`. Use polynomial arithmetic with `[mul_nonneg hA0 key]`.
-/
lemma dhPos_term_nonneg {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    0 ≤ (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n).re
      + (term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [dhPos_term_real, dhPos_term_real, dhPos_term, dhPos_term]
  simp only [Complex.re_ofReal_mul]
  have hA0 : 0 ≤ (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  have hz1 : ‖(n : ℂ) ^ ((γ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    simp
  have hw : -1 ≤ (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    have hnorm : ‖χ n / (n : ℂ) ^ ((γ : ℂ) * I)‖ ≤ 1 := by
      rw [norm_div, hz1, div_one]
      exact DirichletCharacter.norm_le_one χ _
    have h2 := Complex.abs_re_le_norm (χ n / (n : ℂ) ^ ((γ : ℂ) * I))
    linarith [(abs_le.1 h2).1]
  have key : 0 ≤ ((1 : DirichletCharacter ℂ q) n).re + (χ₁ n).re + (χ n / (n : ℂ) ^ ((γ : ℂ) * I)).re +
      ((χ * χ₁) n / (n : ℂ) ^ ((γ : ℂ) * I)).re := by
    by_cases hu : IsUnit (n : ZMod q)
    · have h1n : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
      have hsq : χ₁ n * χ₁ n = 1 := by
        have e := congrArg (fun ψ : DirichletCharacter ℂ q => ψ n) h1
        simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hu] using e
      have hχ₁ : χ₁ n = 1 ∨ χ₁ n = -1 := by
        have h' : (χ₁ n - 1) * (χ₁ n + 1) = 0 := by linear_combination hsq
        rcases mul_eq_zero.1 h' with h | h
        · left
          linear_combination h
        · right
          linear_combination h
      rw [MulChar.mul_apply, h1n]
      rcases hχ₁ with h | h
      · rw [h, mul_one]
        simp only [Complex.one_re]
        linarith
      · rw [h]
        simp only [Complex.one_re, Complex.neg_re, mul_neg, mul_one, neg_div]
        linarith
    · have h0 : ∀ ψ : DirichletCharacter ℂ q, ψ n = 0 := fun ψ => MulChar.map_nonunit ψ hu
      simp [h0]
  nlinarith [mul_nonneg hA0 key]

/- English proof (translation)
Introduce `M _ χ₁ χ γ σ k h1 hσ`. Establish `hs1 : 1 < ((σ : ℂ)).re` using `by simpa using hσ`. Establish `hs2 : 1 < ((σ : ℂ) + γ * I).re` using `by simpa using hσ`. Establish `H1` using `dhPos_hasSum (1 : DirichletCharacter ℂ M) k hs1`. Establish `H2` using `dhPos_hasSum χ₁ k hs1`.

Establish `H3` using `dhPos_hasSum χ k hs2`. Establish `H4` using `dhPos_hasSum (χ * χ₁) k hs2`. Establish `Hall` using `((H1.add H2).add H3).add H4`. Rewrite using `[mul_add, mul_add, mul_add, Complex.add_re, Complex.add_re, Complex.add_re]`. Conclude with `Hall.nonneg (fun n => dhPos_term_nonneg χ₁ χ h1 k σ γ n)`.
-/
theorem deuring_heilbronn_positivity : DHPos := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have H1 := dhPos_hasSum (1 : DirichletCharacter ℂ M) k hs1
  have H2 := dhPos_hasSum χ₁ k hs1
  have H3 := dhPos_hasSum χ k hs2
  have H4 := dhPos_hasSum (χ * χ₁) k hs2
  have Hall := ((H1.add H2).add H3).add H4
  rw [mul_add, mul_add, mul_add, Complex.add_re, Complex.add_re, Complex.add_re]
  exact Hall.nonneg (fun n => dhPos_term_nonneg χ₁ χ h1 k σ γ n)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
