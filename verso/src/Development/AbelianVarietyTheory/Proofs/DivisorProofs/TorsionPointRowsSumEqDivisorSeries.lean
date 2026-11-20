import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumLambertDoubleSeriesDivisorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumResidueClassSplitBySignStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointRowSumEqQExpansionSeriesStatement

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.RowsSummed

/- English proof (translation)
Unfold `ch`. Rewrite using `[Complex.norm_exp]`. Simplify using `[Complex.div_re]`.
-/
theorem norm_ch (N : ℕ) (j : ZMod N) : ‖ch N j‖ = 1 := by
  unfold ch
  rw [Complex.norm_exp]
  simp [Complex.div_re]

/- English proof (translation)
Rewrite using `[Complex.norm_exp, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_lt_exp]`. Establish `hN : (0 : ℝ) < N` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)`. Establish `hτ` using `τ.im_pos`. Establish `: ((2 * (Real.pi : ℂ) * Complex.I) * τ / N).re = -(2 * Real.pi * τ.im) / N`. Simplify using `[Complex.div_re, Complex.mul_re, Complex.mul_im]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Apply `div_neg_of_neg_of_pos _ hN` to reduce the goal to its premises. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_q_lt (N : ℕ) [NeZero N] (τ : ℍ) :
    ‖Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N)‖ < 1 := by
  rw [Complex.norm_exp, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_lt_exp]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hτ := τ.im_pos
  have : ((2 * (Real.pi : ℂ) * Complex.I) * τ / N).re = -(2 * Real.pi * τ.im) / N := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    field_simp
  rw [this]
  apply div_neg_of_neg_of_pos _ hN
  have := Real.pi_pos
  nlinarith

/- English proof (translation)
Introduce `N _ e τ x S he hS`. Use `set q : ℂ := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq`. Use `set K : ℂ := (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ)`. Use `set R : ℤ → ℂ := fun k => ∑' m : ℤ, 1 / (((k : ℂ) * τ + ((x 1).val : ℂ)) / N + m) ^ (e + 1) with hR`. Establish `hN : (N : ℂ) ≠ 0` using `by exact_mod_cast NeZero.ne N`.

Establish `hfR : (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) = fun n : ℤ => R (((x 0).val : ℤ) + n * N)`. Use function extensionality and compare the values at `n`. Simplify using `only [hR]`. Use `congr 1`. Use function extensionality and compare the values at `m`.

Use `congr 3`. Unfold `tors`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hS` using `[hfR]`. Establish `hsplit` using `GlobalTheory.T.tsum_residueClass_split_by_sign N (x 0) R hS.summable`. Set `c₁ : ℕ → ℕ → ℂ` to `fun d m => if ((d : ℕ) : ZMod N) = x 0 then ch N ((m : ZMod N) * x 1) else 0`. Set `c₂ : ℕ → ℕ → ℂ` to `fun d m => if ((d : ℕ) : ZMod N) = -x 0 then ch N (-((m : ZMod N) * x 1)) else 0`. Establish `hq1 : ‖q‖ < 1` using `norm_q_lt N τ`.

Establish `hc₁ : ∀ d m, ‖c₁ d m‖ ≤ 1`. Introduce `d m`. Simplify using `only [c₁]`. Use `split_ifs`. Rewrite using `[norm_ch]`.

Simplify using the standard rewrite rules. Establish `hc₂ : ∀ d m, ‖c₂ d m‖ ≤ 1`. Introduce `d m`. Simplify using `only [c₂]`. Use `split_ifs`.

Rewrite using `[norm_ch]`. Simplify using the standard rewrite rules. Establish `h₁` using `GlobalTheory.T.hasSum_lambert_double_series_divisors e q c₁ hq1 hc₁`. Establish `h₂` using `GlobalTheory.T.hasSum_lambert_double_series_divisors e q c₂ hq1 hc₂`. Use `set T₁ := ∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₁ d m * q ^ ((d : ℕ) * (m : ℕ))`.

Use `set T₂ := ∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₂ d m * q ^ ((d : ℕ) * (m : ℕ))`. Use `⟨T₁ + (-1) ^ (e + 1) * T₂, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `h₁.add (h₂.mul_left ((-1) ^ (e + 1)))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Simplify using `only [cSum, c₁, c₂]`. Rewrite using `[show ∀ A B C D : ℂ, A * D + C * (B * D) = (A + C * B) * D from fun A B C D => by ring]`. Use `congr 1`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hS.tsum_eq, hsplit]`. Establish `hpos : ∀ d : ℕ+, (if ((d : ℕ) : ZMod N) = x 0 then R ((d : ℕ) : ℤ) else 0) = K * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₁ d m * q ^ ((d : ℕ) * (m : ℕ))`. Introduce `d`. Simplify using `only [c₁]`.

Use `split_ifs with hd`. Use `(GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series N e τ (x 1) d he).1` as an intermediate fact. Simplify using `only [hR]`. Use `push_cast`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `hneg : ∀ d : ℕ+, (if ((d : ℕ) : ZMod N) = -x 0 then R (-((d : ℕ) : ℤ)) else 0) = K * ((-1) ^ (e + 1) * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₂ d m * q ^ ((d : ℕ) * (m : ℕ)))`. Introduce `d`. Simplify using `only [c₂]`. Use `split_ifs with hd`.

Use `(GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series N e τ (x 1) d he).2` as an intermediate fact. Simplify using `only [hR]`. Use `push_cast`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Rewrite using `[tsum_congr hpos, tsum_congr hneg, tsum_mul_left, tsum_mul_left, tsum_mul_left]`. Establish `h0 : R 0 = ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1)`. Simplify using `[hR]`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (x : Fin 2 → ZMod N) (S : ℂ), 1 ≤ e → HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) S → ∃ T : ℂ, HasSum (fun k : ℕ => cSum N e ((-1) ^ (e + 1)) x k * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T ∧ S = (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1) else 0) + (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * T := by
  intro N _ e τ x S he hS
  set q : ℂ := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq
  set K : ℂ := (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ)
  set R : ℤ → ℂ := fun k => ∑' m : ℤ, 1 / (((k : ℂ) * τ + ((x 1).val : ℂ)) / N + m) ^ (e + 1) with hR
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hfR : (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) =
      fun n : ℤ => R (((x 0).val : ℤ) + n * N) := by
    funext n
    simp only [hR]
    congr 1
    funext m
    congr 3
    unfold tors
    push_cast
    field_simp
    ring
  rw [hfR] at hS
  have hsplit := GlobalTheory.T.tsum_residueClass_split_by_sign N (x 0) R hS.summable
  let c₁ : ℕ → ℕ → ℂ := fun d m => if ((d : ℕ) : ZMod N) = x 0 then ch N ((m : ZMod N) * x 1) else 0
  let c₂ : ℕ → ℕ → ℂ := fun d m => if ((d : ℕ) : ZMod N) = -x 0 then ch N (-((m : ZMod N) * x 1)) else 0
  have hq1 : ‖q‖ < 1 := norm_q_lt N τ
  have hc₁ : ∀ d m, ‖c₁ d m‖ ≤ 1 := by
    intro d m
    simp only [c₁]
    split_ifs
    · rw [norm_ch]
    · simp
  have hc₂ : ∀ d m, ‖c₂ d m‖ ≤ 1 := by
    intro d m
    simp only [c₂]
    split_ifs
    · rw [norm_ch]
    · simp
  have h₁ := GlobalTheory.T.hasSum_lambert_double_series_divisors e q c₁ hq1 hc₁
  have h₂ := GlobalTheory.T.hasSum_lambert_double_series_divisors e q c₂ hq1 hc₂
  set T₁ := ∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₁ d m * q ^ ((d : ℕ) * (m : ℕ))
  set T₂ := ∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₂ d m * q ^ ((d : ℕ) * (m : ℕ))
  refine ⟨T₁ + (-1) ^ (e + 1) * T₂, ?_, ?_⟩
  · have h := h₁.add (h₂.mul_left ((-1) ^ (e + 1)))
    convert h using 1
    funext k
    simp only [cSum, c₁, c₂]
    rw [show ∀ A B C D : ℂ, A * D + C * (B * D) = (A + C * B) * D from fun A B C D => by ring]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  · rw [← hS.tsum_eq, hsplit]
    have hpos : ∀ d : ℕ+, (if ((d : ℕ) : ZMod N) = x 0 then R ((d : ℕ) : ℤ) else 0) =
        K * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₁ d m * q ^ ((d : ℕ) * (m : ℕ)) := by
      intro d
      simp only [c₁]
      split_ifs with hd
      · have := (GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series N e τ (x 1) d he).1
        simp only [hR]
        push_cast
        rw [this]
      · simp
    have hneg : ∀ d : ℕ+, (if ((d : ℕ) : ZMod N) = -x 0 then R (-((d : ℕ) : ℤ)) else 0) =
        K * ((-1) ^ (e + 1) * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c₂ d m * q ^ ((d : ℕ) * (m : ℕ))) := by
      intro d
      simp only [c₂]
      split_ifs with hd
      · have := (GlobalTheory.T.torsionPoint_rowSum_eq_qExpansion_series N e τ (x 1) d he).2
        simp only [hR]
        push_cast
        rw [this]
      · simp
    rw [tsum_congr hpos, tsum_congr hneg, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    have h0 : R 0 = ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1) := by
      simp [hR]
    rw [h0]
    ring

end GlobalTheory.WpFam.RowsSummed
