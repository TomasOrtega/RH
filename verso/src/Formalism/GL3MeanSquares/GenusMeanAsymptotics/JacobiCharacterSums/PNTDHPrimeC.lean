import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeB
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailMertens

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter

def dhprF {M : ℕ} (χ₁ : DirichletCharacter ℂ M) (k : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `key : Real.exp ((σ - 1) * v) * n ≤ (n : ℝ) ^ σ`. Establish `e1 : (n : ℝ) ^ σ = (n : ℝ) ^ (σ - 1) * n`. Rewrite using `[← Real.rpow_add_one hn0.ne']`. Put the polynomial expressions in normal form.

Rewrite using `[e1]`. Apply `mul_le_mul_of_nonneg_right _ hn0.le` to reduce the goal to its premises. Rewrite using `[Real.rpow_def_of_pos hn0]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hv.le) (sub_nonneg.mpr hσ)]`.

Establish `e2 : Real.exp (-((σ - 1) * v)) / n = 1 / (Real.exp ((σ - 1) * v) * n)`. Rewrite using `[Real.exp_neg]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`. Conclude with `one_div_le_one_div_of_le (by positivity) key`.
-/
lemma dhpr_rpow_le {σ : ℝ} (hσ : 1 ≤ σ) {n v : ℕ} (hn : 1 ≤ n) (hv : (v : ℝ) < Real.log n) :
    1 / (n : ℝ) ^ σ ≤ Real.exp (-((σ - 1) * v)) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : Real.exp ((σ - 1) * v) * n ≤ (n : ℝ) ^ σ := by
    have e1 : (n : ℝ) ^ σ = (n : ℝ) ^ (σ - 1) * n := by
      rw [← Real.rpow_add_one hn0.ne']
      ring_nf
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ hn0.le
    rw [Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.le) (sub_nonneg.mpr hσ)]
  have e2 : Real.exp (-((σ - 1) * v)) / n = 1 / (Real.exp ((σ - 1) * v) * n) := by
    rw [Real.exp_neg]
    field_simp
  rw [e2]
  exact one_div_le_one_div_of_le (by positivity) key

/- English proof (translation)
Establish `hterm : ∀ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n ≤ 2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) * ((∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n)`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Ioc]`. Establish `hgt : Real.exp (v : ℝ) < n` using `(Nat.floor_lt (Real.exp_pos _).le).mp hn.1`. Establish `hle : (n : ℝ) ≤ Real.exp ((v + 1 : ℕ) : ℝ)` using `(Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2`.

Establish `hnpos : (0 : ℝ) < n` using `lt_trans (Real.exp_pos _) hgt`. Establish `hn1 : 1 ≤ n`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `interval_cases n`.

Simplify using `at hnpos`. Establish `hlogv : (v : ℝ) < Real.log n`. Rewrite using `[Real.lt_log_iff_exp_lt hnpos]`. Conclude with `hgt`. Establish `hlog1 : Real.log n ≤ (v : ℝ) + 1`.

Establish `h5` using `Real.log_le_log hnpos hle`. Rewrite `h5` using `[Real.log_exp]`. Move the coercions through the operations in `at h5`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog0 : 0 ≤ Real.log n` using `le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg v) hlogv)`.

Establish `hz` using `dhpr_r_nonneg χ₁ h1 n`. Establish `hr` using `dhpr_rpow_le hσ hn1 hlogv`. Establish `hp1 : (Real.log n) ^ (k + 1) ≤ ((v : ℝ) + 1) ^ (k + 1)` using `pow_le_pow_left₀ hlog0 hlog1 _`. Establish `hq0 : 0 ≤ (Real.log n) ^ (k + 1)` using `pow_nonneg hlog0 _`. Rewrite using `[← dhpr_zetaMul_eq_sum]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp1 hz) (by norm_num)) hr (by positivity) (by positivity)` to reduce the goal to its premises. Use `_ = _ := by ring`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma dhpr_block {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ : ℝ} (hσ : 1 ≤ σ) (v : ℕ) (B : ℝ)
    (hH : ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤ B) :
    ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n ≤
      2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) * B := by
  have hterm : ∀ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
      dhprF χ₁ k σ n ≤ 2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
        ((∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hgt : Real.exp (v : ℝ) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hn.1
    have hle : (n : ℝ) ≤ Real.exp ((v + 1 : ℕ) : ℝ) := (Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hgt
    have hn1 : 1 ≤ n := by
      by_contra hc
      push_neg at hc
      interval_cases n
      simp at hnpos
    have hlogv : (v : ℝ) < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hnpos]
      exact hgt
    have hlog1 : Real.log n ≤ (v : ℝ) + 1 := by
      have h5 := Real.log_le_log hnpos hle
      rw [Real.log_exp] at h5
      push_cast at h5
      linarith
    have hlog0 : 0 ≤ Real.log n := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg v) hlogv)
    have hz := dhpr_r_nonneg χ₁ h1 n
    have hr := dhpr_rpow_le hσ hn1 hlogv
    have hp1 : (Real.log n) ^ (k + 1) ≤ ((v : ℝ) + 1) ^ (k + 1) := pow_le_pow_left₀ hlog0 hlog1 _
    have hq0 : 0 ≤ (Real.log n) ^ (k + 1) := pow_nonneg hlog0 _
    rw [← dhpr_zetaMul_eq_sum]
    calc dhprF χ₁ k σ n ≤ 2 * (Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ :=
          dhpr_term_le_r χ₁ h1 k n σ
      _ = 2 * ((Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re) * (1 / (n : ℝ) ^ σ) := by ring
      _ ≤ 2 * (((v : ℝ) + 1) ^ (k + 1) * (zetaMul χ₁ n).re) * (Real.exp (-((σ - 1) * v)) / n) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp1 hz) (by norm_num)) hr
            (by positivity) (by positivity)
      _ = _ := by ring
  calc _ ≤ ∑ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
          ((∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n) := Finset.sum_le_sum hterm
    _ = 2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
          ∑ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
            (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

/- English proof (translation)
Establish `hy : (2 : ℝ) ≤ Real.exp (v0 : ℝ)`. Establish `hv1 : (1 : ℝ) ≤ v0` using `by exact_mod_cast hv0`. Combine the equalities or inequalities in the displayed calculation. Establish `hM` using `hMert _ hy`. Rewrite `hM` using `[Real.log_exp]`.

Establish `hIoc : Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊ = Finset.Icc 1 ⌊Real.exp (v0 : ℝ)⌋₊`. Use extensionality with `n`. Simplify using `only [Finset.mem_Ioc, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Establish `hterm : ∀ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n ≤ 2 * (v0 : ℝ) ^ k * (Λ n / n)`.

Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Ioc]`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn.1`. Establish `hlog0 : 0 ≤ Real.log n` using `Real.log_nonneg hn1`. Establish `hlog : Real.log n ≤ v0`.

Establish `hnle : (n : ℝ) ≤ Real.exp v0` using `(Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2`. Combine the equalities or inequalities in the displayed calculation. Establish `hΛ : 0 ≤ (Λ n : ℝ) / (n : ℝ)` using `div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
lemma dhpr_small {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ : ℝ} (hσ : 1 ≤ σ) (v0 : ℕ) (hv0 : 1 ≤ v0) {CT : ℝ} (hCT : 0 ≤ CT)
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y) :
    ∑ n ∈ Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n ≤ 2 * CT * (v0 : ℝ) ^ (k + 1) := by
  have hy : (2 : ℝ) ≤ Real.exp (v0 : ℝ) := by
    have hv1 : (1 : ℝ) ≤ v0 := by exact_mod_cast hv0
    calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ Real.exp v0 := Real.exp_le_exp.mpr hv1
  have hM := hMert _ hy
  rw [Real.log_exp] at hM
  have hIoc : Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊ = Finset.Icc 1 ⌊Real.exp (v0 : ℝ)⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n ≤ 2 * (v0 : ℝ) ^ k * (Λ n / n) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlog : Real.log n ≤ v0 := by
      have hnle : (n : ℝ) ≤ Real.exp v0 := (Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2
      calc Real.log n ≤ Real.log (Real.exp v0) := Real.log_le_log (by linarith) hnle
        _ = v0 := Real.log_exp _
    have hΛ : 0 ≤ (Λ n : ℝ) / (n : ℝ) := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    calc dhprF χ₁ k σ n ≤ 2 * (Real.log n) ^ k * (Λ n / n) := dhpr_term_le_small χ₁ h1 k n hσ
      _ ≤ 2 * (v0 : ℝ) ^ k * (Λ n / n) := by gcongr
  calc ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, 2 * (v0 : ℝ) ^ k * (Λ n / n) := Finset.sum_le_sum hterm
    _ = 2 * (v0 : ℝ) ^ k * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (v0 : ℝ)⌋₊, Λ n / n := by rw [← Finset.mul_sum, hIoc]
    _ ≤ 2 * (v0 : ℝ) ^ k * (CT * v0) := by gcongr
    _ = 2 * CT * (v0 : ℝ) ^ (k + 1) := by ring

/- English proof (translation)
Establish `h1 : Real.log (Real.exp ((v + 1 : ℕ) : ℝ) / Real.exp (v : ℝ)) = 1`. Rewrite using `[← Real.exp_sub, Real.log_exp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Real.sqrt (Real.exp (v : ℝ)) = Real.exp ((v : ℝ) / 2)`.

Rewrite using `[show Real.exp (v : ℝ) = Real.exp ((v : ℝ) / 2) * Real.exp ((v : ℝ) / 2) by`. Rewrite using `[← Real.exp_add]`. Use the proof step `ring_nf, Real.sqrt_mul_self (Real.exp_pos _).le]`. Rewrite using `[h1, Real.log_exp, h2, Real.exp_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dhpr_hyper_simp (A CH x : ℝ) (v : ℕ) :
    A * Real.log (Real.exp ((v + 1 : ℕ) : ℝ) / Real.exp (v : ℝ))
      + CH * x * (Real.log (Real.exp (v : ℝ)) + 1) / Real.sqrt (Real.exp (v : ℝ)) =
      A + CH * x * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
  have h1 : Real.log (Real.exp ((v + 1 : ℕ) : ℝ) / Real.exp (v : ℝ)) = 1 := by
    rw [← Real.exp_sub, Real.log_exp]
    push_cast
    ring
  have h2 : Real.sqrt (Real.exp (v : ℝ)) = Real.exp ((v : ℝ) / 2) := by
    rw [show Real.exp (v : ℝ) = Real.exp ((v : ℝ) / 2) * Real.exp ((v : ℝ) / 2) by
      rw [← Real.exp_add]; ring_nf, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [h1, Real.log_exp, h2, Real.exp_neg]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
