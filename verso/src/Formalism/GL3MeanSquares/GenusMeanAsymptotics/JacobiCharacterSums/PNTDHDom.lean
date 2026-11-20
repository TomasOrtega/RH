import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPos

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/- English proof (translation)
Establish `habs : abscissaOfAbsConv (↗ψ * ↗Λ) < s.re`. Use `lt_of_le_of_lt (abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) ?_) ?_` and prove the remaining obligations. Introduce `y hy`. Conclude with `LSeriesSummable_twist_vonMangoldt ψ hy`. Conclude with `hs` after adjusting the coercions.

Establish `hopen : IsOpen {z : ℂ | 1 < z.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hev : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ)` using `by filter_upwards [hopen.mem_nhds hs] with z hz`. Establish `hz' : (1 : ℝ) < z.re` using `hz`. Establish `hU : LFunction ψ =ᶠ[nhds z] LSeries (↗ψ)` using `by filter_upwards [hopen.mem_nhds hz'] with w hw`. Conclude with `DirichletCharacter.LFunction_eq_LSeries ψ hw`.

Simplify using `only [negLD]`. Rewrite using `[Filter.EventuallyEq.deriv_eq hU, DirichletCharacter.LFunction_eq_LSeries ψ hz', LSeries_twist_vonMangoldt_eq ψ hz', neg_div]`. Establish `hit : iteratedDeriv k (negLD ψ) s = iteratedDeriv k (LSeries (↗ψ * ↗Λ)) s`. Simplify using `only [← iteratedDerivWithin_univ]`. Use `Filter.EventuallyEq.iteratedDerivWithin_eq ?_ hev.eq_of_nhds` and prove the remaining obligations.

Simplify `hev` using `[nhdsWithin_univ]`. Rewrite using `[hit, LSeries_iteratedDeriv k habs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]`. Simplify using `only [neg_one_sq, one_pow, one_mul]`. Conclude with `(LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using habs)).LSeriesHasSum`.
-/
lemma dhDom_hasSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n ↦ term (logMul^[k] (↗ψ * ↗Λ)) s n)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s) := by
  have habs : abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
    refine lt_of_le_of_lt (abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) ?_) ?_
    · intro y hy
      exact LSeriesSummable_twist_vonMangoldt ψ hy
    · exact_mod_cast hs
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hU : LFunction ψ =ᶠ[nhds z] LSeries (↗ψ) := by
      filter_upwards [hopen.mem_nhds hz'] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    simp only [negLD]
    rw [Filter.EventuallyEq.deriv_eq hU, DirichletCharacter.LFunction_eq_LSeries ψ hz',
      LSeries_twist_vonMangoldt_eq ψ hz', neg_div]
  have hit : iteratedDeriv k (negLD ψ) s = iteratedDeriv k (LSeries (↗ψ * ↗Λ)) s := by
    simp only [← iteratedDerivWithin_univ]
    refine Filter.EventuallyEq.iteratedDerivWithin_eq ?_ hev.eq_of_nhds
    simpa [nhdsWithin_univ] using hev
  rw [hit, LSeries_iteratedDeriv k habs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (by simpa using habs)).LSeriesHasSum

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', logMul, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem logMul_iterate_apply_eq_log_pow_mul (f : ℕ → ℂ) (k n : ℕ) :
    logMul^[k] f n = Complex.log n ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', logMul, ih]
    ring

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn`. Use `set A : ℝ := Real.log n ^ k * Λ n with hA`. Establish `hA0 : 0 ≤ A` using `mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) ArithmeticFunction.vonMangoldt_nonneg`.

Establish `e1 : ∀ c : ℂ, Complex.log n ^ k * (c * ((Λ n : ℝ) : ℂ)) = (A : ℂ) * c`. Introduce `c`. Rewrite using `[hA, ← Complex.natCast_log]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hN : ‖(n : ℂ) ^ ((σ : ℂ) + γ * I)‖ = (n : ℝ) ^ σ`. Rewrite using `[Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]`. Simplify using the standard rewrite rules. Establish `hR : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_natCast, Complex.ofReal_cpow hnpos.le]`.

Establish `hp : 0 < (n : ℝ) ^ σ` using `Real.rpow_pos_of_pos hnpos σ`. Establish `hre : ∀ c : ℝ, ((A : ℂ) * (c : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)).re = A * c / (n : ℝ) ^ σ`. Introduce `c`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]`. Simplify using `only [term_of_ne_zero hn, logMul_iterate_apply_eq_log_pow_mul, Pi.mul_apply, MulChar.coeToFun_mul, e1, hR]`.

Distinguish the cases in `hu : IsUnit (n : ZMod q)`. Take `⟨u, hu'⟩` from `hu`. Rewrite using `[← hu', MulChar.one_apply_coe]`. Establish `hχ : ‖χ u‖ = 1` using `DirichletCharacter.unit_norm_eq_one χ u`. Establish `h1u : χ₁ u * χ₁ u = 1`.

Rewrite using `[← pow_two, ← MulChar.pow_apply_coe, h1, MulChar.one_apply_coe]`. Break down `mul_self_eq_one_iff.mp h1u with h | h` into its components or cases. Rewrite using `[h]`. Use `hre 1` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite using `[this]`. Establish `e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * 1) / (n : ℂ) ^ ((σ : ℂ) + γ * I) = ((2 * A : ℝ) : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, norm_div, norm_mul, hχ, hN, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`.

Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Use `hre 1` as an intermediate fact. Establish `h'` using `hre (-1)`.

Move the coercions through the operations in `at this h'`. Rewrite using `[this, h']`. Establish `e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * -1) / (n : ℂ) ^ ((σ : ℂ) + γ * I) = 0`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, norm_zero]`.

Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree. Simplify using `[MulChar.map_nonunit _ hu]`.
-/
lemma dhDom_term_le {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    ‖term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n
      + term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n‖ ≤
    (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set A : ℝ := Real.log n ^ k * Λ n with hA
  have hA0 : 0 ≤ A :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) ArithmeticFunction.vonMangoldt_nonneg
  have e1 : ∀ c : ℂ, Complex.log n ^ k * (c * ((Λ n : ℝ) : ℂ)) = (A : ℂ) * c := by
    intro c
    rw [hA, ← Complex.natCast_log]
    push_cast
    ring
  have hN : ‖(n : ℂ) ^ ((σ : ℂ) + γ * I)‖ = (n : ℝ) ^ σ := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hR : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnpos.le]
  have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
  have hre : ∀ c : ℝ, ((A : ℂ) * (c : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)).re = A * c / (n : ℝ) ^ σ := by
    intro c
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [term_of_ne_zero hn, logMul_iterate_apply_eq_log_pow_mul, Pi.mul_apply, MulChar.coeToFun_mul, e1, hR]
  by_cases hu : IsUnit (n : ZMod q)
  · obtain ⟨u, hu'⟩ := hu
    rw [← hu', MulChar.one_apply_coe]
    have hχ : ‖χ u‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
    have h1u : χ₁ u * χ₁ u = 1 := by
      rw [← pow_two, ← MulChar.pow_apply_coe, h1, MulChar.one_apply_coe]
    rcases mul_self_eq_one_iff.mp h1u with h | h
    · rw [h]
      have := hre 1
      push_cast at this
      rw [this]
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * 1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = ((2 * A : ℝ) : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) := by
        push_cast
        ring
      rw [e2, norm_div, norm_mul, hχ, hN, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      apply le_of_eq
      ring
    · rw [h]
      have := hre 1
      have h' := hre (-1)
      push_cast at this h'
      rw [this, h']
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * -1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = 0 := by
        ring
      rw [e2, norm_zero]
      apply le_of_eq
      ring
  · simp [MulChar.map_nonunit _ hu]

/- English proof (translation)
Introduce `M _ χ₁ χ γ σ k h1 hσ`. Establish `hs : 1 < ((σ : ℂ) + γ * I).re` using `by simpa using hσ`. Establish `hs0 : 1 < (σ : ℂ).re` using `by simpa using hσ`. Establish `hA` using `dhDom_hasSum χ k hs`. Establish `hB` using `dhDom_hasSum (χ * χ₁) k hs`.

Establish `hC` using `dhDom_hasSum (1 : DirichletCharacter ℂ M) k hs0`. Establish `hD` using `dhDom_hasSum χ₁ k hs0`. Establish `hbound` using `HasSum.norm_le_of_bounded (hA.add hB) (Complex.hasSum_re (hC.add hD)) (fun n ↦ by`. Rewrite using `[Complex.add_re]`. Conclude with `dhDom_term_le χ₁ χ h1 k σ γ n)`.

Establish `e1 : ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I) + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ = ‖(-1 : ℂ) ^ k * iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I) + (-1 : ℂ) ^ k * iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖`. Rewrite using `[← mul_add, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Rewrite using `[e1, mul_add]`. Conclude with `hbound`.
-/
theorem deuring_heilbronn_dominant : DHDom := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hA := dhDom_hasSum χ k hs
  have hB := dhDom_hasSum (χ * χ₁) k hs
  have hC := dhDom_hasSum (1 : DirichletCharacter ℂ M) k hs0
  have hD := dhDom_hasSum χ₁ k hs0
  have hbound := HasSum.norm_le_of_bounded (hA.add hB) (Complex.hasSum_re (hC.add hD))
    (fun n ↦ by
      rw [Complex.add_re]
      exact dhDom_term_le χ₁ χ h1 k σ γ n)
  have e1 : ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
      + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ =
      ‖(-1 : ℂ) ^ k * iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
        + (-1 : ℂ) ^ k * iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ := by
    rw [← mul_add, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [e1, mul_add]
  exact hbound

end Formalism.HermitianLattices.Ext.PrimesInProgressions
