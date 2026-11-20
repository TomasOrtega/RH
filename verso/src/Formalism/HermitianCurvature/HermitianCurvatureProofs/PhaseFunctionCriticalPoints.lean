import Formalism.HermitianCurvature.StatementG

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.G1

open Formalism.FourierDecayAlt.G

/- English proof (translation)
Use `Finset.prod_update_of_mem (Finset.mem_univ k) x (x k)` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`. Then use the resulting hypothesis.
-/
theorem prod_split {n : ℕ} (x : Fin n → ℂ) (k : Fin n) :
    ∏ j, x j = x k * ∏ j ∈ univ \ {k}, x j := by
  have := Finset.prod_update_of_mem (Finset.mem_univ k) x (x k)
  rwa [Function.update_eq_self] at this

/- English proof (translation)
Unfold `g0`. Rewrite using `[Finset.prod_update_of_mem (mem_univ k), Finset.sum_update_of_mem (mem_univ k)]`.
-/
theorem phase_function_update {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (k : Fin n) (ξ : ℂ) :
    g0 D' (Function.update x k ξ) =
      ξ + ∑ j ∈ univ \ {k}, x j + D' / (ξ * ∏ j ∈ univ \ {k}, x j) := by
  unfold g0
  rw [Finset.prod_update_of_mem (mem_univ k), Finset.sum_update_of_mem (mem_univ k)]

/- English proof (translation)
Unfold `dg0`. Rewrite using `[Finset.prod_update_of_mem (mem_univ j)]`.
-/
theorem phase_deriv_update {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (j i : Fin n) (ξ : ℂ) :
    dg0 D' (Function.update x j ξ) i =
      1 - D' / (ξ * ∏ l ∈ univ \ {j}, x l) / (Function.update x j ξ i) := by
  unfold dg0
  rw [Finset.prod_update_of_mem (mem_univ j)]

/- English proof (translation)
Establish `h` using `(hasDerivAt_const a c).div ((hasDerivAt_id' a).mul_const Q) (mul_ne_zero ha hQ)`. Use `h.congr_deriv ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_inv_lin (c Q a : ℂ) (ha : a ≠ 0) (hQ : Q ≠ 0) :
    HasDerivAt (fun ξ : ℂ => c / (ξ * Q)) (-(c / (a * Q) / a)) a := by
  have h := (hasDerivAt_const a c).div ((hasDerivAt_id' a).mul_const Q) (mul_ne_zero ha hQ)
  refine h.congr_deriv ?_
  field_simp
  ring

/- English proof (translation)
Establish `h` using `(hasDerivAt_inv_lin c Q a ha hQ).div (hasDerivAt_id' a) ha`. Use `h.congr_deriv ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_inv_sq (c Q a : ℂ) (ha : a ≠ 0) (hQ : Q ≠ 0) :
    HasDerivAt (fun ξ : ℂ => c / (ξ * Q) / ξ) (-(2 * c / (a * Q * a * a))) a := by
  have h := (hasDerivAt_inv_lin c Q a ha hQ).div (hasDerivAt_id' a) ha
  refine h.congr_deriv ?_
  field_simp
  ring

/- English proof (translation)
Establish `hP0 : (∏ k, x k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun k _ => hx k)`. Take `⟨P, hP⟩ : ∃ P, P = ∏ k, x k` from `⟨_, rfl⟩`. Rewrite `hP0` using `[← hP]`. Take `⟨ρ, hρ⟩ : ∃ ρ, ρ = D' / P` from `⟨_, rfl⟩`. Take `⟨e, he⟩ : ∃ e : Fin (m + 1) → ℂ, e = fun k => dg0 D' x k` from `⟨_, rfl⟩`.

Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `he1 : ∀ k, (1 - e k) * x k = ρ`. Introduce `k`. Use `hx k` as an intermediate fact. Simplify using `only [he, dg0, ← hP, ← hρ]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hη8 : η ≤ 1 / 8`. Use `hη'.trans ?_` and prove the remaining obligations. Apply the tactic sequence `apply one_div_le_one_div_of_le <;> linarith`.

Establish `hen : ∀ k, ‖e k‖ < η` using `by intro k; rw [he]; exact h k`. Establish `hen2 : ∀ k, ‖-e k‖ ≤ 1 / 2`. Introduce `k`. Rewrite using `[norm_neg]`. Combine the linear relations using `[hen k]`.

Establish `h1e : ∀ k, 7 / 8 ≤ ‖1 - e k‖`. Introduce `k`. Use `norm_sub_norm_le (1 : ℂ) (e k)` as an intermediate fact. Rewrite `this` using `[norm_one]`. Combine the linear relations using `[hen k]`.

Establish `h1e0 : ∀ k, 1 - e k ≠ 0`. Introduce `k hk`. Use `h1e k` as an intermediate fact. Rewrite `this` using `[hk, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨L, hL⟩ : ∃ L : ℂ, L = (∑ k, Complex.log (1 + -e k)) / ((m : ℂ) + 2)` from `⟨_, rfl⟩`. Establish `hm2 : ((m : ℂ) + 2) ≠ 0`. Establish `: ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ)` using `by push_cast; ring`. Rewrite using `[this]; exact Nat.cast_ne_zero.mpr (by omega)`. Establish `hm2n : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2`.

Establish `: ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`. Establish `hLn : ‖L‖ ≤ 3 / 2 * η`. Rewrite using `[hL, norm_div, hm2n, div_le_iff₀ (by linarith)]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `k _`. Use `Complex.norm_log_one_add_half_le_self (hen2 k)` as an intermediate fact. Rewrite `this` using `[norm_neg]`. Combine the linear relations using `[hen k]`.

Use `_ = ((m : ℝ) + 1) * (3 / 2 * η) := by simp`. Use `_ ≤ 3 / 2 * η * ((m : ℝ) + 2) := by nlinarith`. Establish `hexp : Complex.exp L ^ (m + 2) = ∏ k, (1 - e k)`. Rewrite using `[← Complex.exp_nat_mul]`. Establish `: ((m + 2 : ℕ) : ℂ) * L = ∑ k, Complex.log (1 + -e k)`.

Rewrite using `[hL]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Complex.exp_sum]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `k _`. Rewrite using `[Complex.exp_log]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← sub_eq_add_neg]`. Conclude with `h1e0 k`.

Establish `hE0 : (∏ k, (1 - e k)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun k _ => h1e0 k)`. Establish `hρpow : ρ ^ (m + 1) = (∏ k, (1 - e k)) * P`. Rewrite using `[hP, ← Finset.prod_mul_distrib]`. Repeatedly rewrite using `[he1]`. Simplify using the standard rewrite rules.

Establish `hρP : ρ * P = D'` using `by rw [hρ]; field_simp`. Use `⟨ρ * Complex.exp (-L), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, Complex.exp_neg, inv_pow, hexp, pow_succ, hρpow, ← hρP]`. Clear the denominators using the available nonvanishing facts. Introduce `k`.

Establish `hzL : ρ * Complex.exp (-L) * Complex.exp L = ρ`. Rewrite using `[mul_assoc, ← Complex.exp_add]`. Simplify using the standard rewrite rules. Establish `key : (x k - ρ * Complex.exp (-L)) * (1 - e k) = ρ * Complex.exp (-L) * (Complex.exp L - 1 + e k)`. Establish `h1` using `he1 k`.

Take the linear combination `h1 - hzL`. Establish `hnum : ‖Complex.exp L - 1 + e k‖ ≤ 4 * η`. Establish `h1 : ‖Complex.exp L - 1‖ ≤ 2 * ‖L‖` using `Complex.norm_exp_sub_one_le (by linarith)`. Establish `h2` using `norm_add_le (Complex.exp L - 1) (e k)`. Combine the linear relations using `[hen k]`.

Establish `hk` using `congrArg norm key`. Rewrite `hk` using `[norm_mul, norm_mul]`. Establish `hz0 : 0 ≤ ‖ρ * Complex.exp (-L)‖` using `norm_nonneg _`. Establish `hx0 : 0 ≤ ‖x k - ρ * Complex.exp (-L)‖` using `norm_nonneg _`. Establish `h3 : ‖x k - ρ * Complex.exp (-L)‖ * (7 / 8) ≤ ‖ρ * Complex.exp (-L)‖ * (4 * η)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 0 ≤ ‖ρ * Complex.exp (-L)‖ * η` using `mul_nonneg hz0 hη.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gradSmall6 (m : ℕ) (D' : ℂ) (hD : D' ≠ 0) (x : Fin (m + 1) → ℂ) (hx : ∀ k, x k ≠ 0)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / (4 * ((m : ℝ) + 2))) (h : ∀ k, ‖dg0 D' x k‖ < η) :
    ∃ z : ℂ, z ^ (m + 2) = D' ∧ ∀ k, ‖x k - z‖ ≤ 6 * η * ‖z‖ := by
  have hP0 : (∏ k, x k) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hx k)
  obtain ⟨P, hP⟩ : ∃ P, P = ∏ k, x k := ⟨_, rfl⟩
  rw [← hP] at hP0
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = D' / P := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Fin (m + 1) → ℂ, e = fun k => dg0 D' x k := ⟨_, rfl⟩
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have he1 : ∀ k, (1 - e k) * x k = ρ := by
    intro k
    have := hx k
    simp only [he, dg0, ← hP, ← hρ]
    field_simp
    ring
  have hη8 : η ≤ 1 / 8 := by
    refine hη'.trans ?_
    apply one_div_le_one_div_of_le <;> linarith
  have hen : ∀ k, ‖e k‖ < η := by intro k; rw [he]; exact h k
  have hen2 : ∀ k, ‖-e k‖ ≤ 1 / 2 := by
    intro k; rw [norm_neg]; linarith [hen k]
  have h1e : ∀ k, 7 / 8 ≤ ‖1 - e k‖ := by
    intro k
    have := norm_sub_norm_le (1 : ℂ) (e k)
    rw [norm_one] at this
    linarith [hen k]
  have h1e0 : ∀ k, 1 - e k ≠ 0 := by
    intro k hk
    have := h1e k
    rw [hk, norm_zero] at this
    linarith
  obtain ⟨L, hL⟩ : ∃ L : ℂ, L = (∑ k, Complex.log (1 + -e k)) / ((m : ℂ) + 2) := ⟨_, rfl⟩
  have hm2 : ((m : ℂ) + 2) ≠ 0 := by
    have : ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact Nat.cast_ne_zero.mpr (by omega)
  have hm2n : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 := by
    have : ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hLn : ‖L‖ ≤ 3 / 2 * η := by
    rw [hL, norm_div, hm2n, div_le_iff₀ (by linarith)]
    calc ‖∑ k, Complex.log (1 + -e k)‖ ≤ ∑ k : Fin (m + 1), ‖Complex.log (1 + -e k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin (m + 1), 3 / 2 * η := by
          apply Finset.sum_le_sum
          intro k _
          have := Complex.norm_log_one_add_half_le_self (hen2 k)
          rw [norm_neg] at this
          linarith [hen k]
      _ = ((m : ℝ) + 1) * (3 / 2 * η) := by simp
      _ ≤ 3 / 2 * η * ((m : ℝ) + 2) := by nlinarith
  have hexp : Complex.exp L ^ (m + 2) = ∏ k, (1 - e k) := by
    rw [← Complex.exp_nat_mul]
    have : ((m + 2 : ℕ) : ℂ) * L = ∑ k, Complex.log (1 + -e k) := by
      rw [hL]; push_cast; field_simp
    rw [this, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro k _
    rw [Complex.exp_log]
    · ring
    · rw [← sub_eq_add_neg]; exact h1e0 k
  have hE0 : (∏ k, (1 - e k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => h1e0 k)
  have hρpow : ρ ^ (m + 1) = (∏ k, (1 - e k)) * P := by
    rw [hP, ← Finset.prod_mul_distrib]
    simp_rw [he1]
    simp
  have hρP : ρ * P = D' := by rw [hρ]; field_simp
  refine ⟨ρ * Complex.exp (-L), ?_, ?_⟩
  · rw [mul_pow, Complex.exp_neg, inv_pow, hexp, pow_succ, hρpow, ← hρP]
    field_simp
  · intro k
    have hzL : ρ * Complex.exp (-L) * Complex.exp L = ρ := by
      rw [mul_assoc, ← Complex.exp_add]; simp
    have key : (x k - ρ * Complex.exp (-L)) * (1 - e k) =
        ρ * Complex.exp (-L) * (Complex.exp L - 1 + e k) := by
      have h1 := he1 k
      linear_combination h1 - hzL
    have hnum : ‖Complex.exp L - 1 + e k‖ ≤ 4 * η := by
      have h1 : ‖Complex.exp L - 1‖ ≤ 2 * ‖L‖ := Complex.norm_exp_sub_one_le (by linarith)
      have h2 := norm_add_le (Complex.exp L - 1) (e k)
      linarith [hen k]
    have hk := congrArg norm key
    rw [norm_mul, norm_mul] at hk
    have hz0 : 0 ≤ ‖ρ * Complex.exp (-L)‖ := norm_nonneg _
    have hx0 : 0 ≤ ‖x k - ρ * Complex.exp (-L)‖ := norm_nonneg _
    have h3 : ‖x k - ρ * Complex.exp (-L)‖ * (7 / 8) ≤ ‖ρ * Complex.exp (-L)‖ * (4 * η) :=
      calc ‖x k - ρ * Complex.exp (-L)‖ * (7 / 8)
          ≤ ‖x k - ρ * Complex.exp (-L)‖ * ‖1 - e k‖ := mul_le_mul_of_nonneg_left (h1e k) hx0
        _ = ‖ρ * Complex.exp (-L)‖ * ‖Complex.exp L - 1 + e k‖ := hk
        _ ≤ ‖ρ * Complex.exp (-L)‖ * (4 * η) := mul_le_mul_of_nonneg_left hnum hz0
    have h4 : 0 ≤ ‖ρ * Complex.exp (-L)‖ * η := mul_nonneg hz0 hη.le
    nlinarith

/- English proof (translation)
Rewrite using `[Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]`. Repeatedly rewrite using `[← Finset.card_filter]`. Establish `: ∀ y : Fin n, (univ.filter (fun x : Fin n => x < y)).card = (y : ℕ)`. Introduce `y`. Rewrite using `[show univ.filter (fun x : Fin n => x < y) = Finset.Iio y by ext; simp]`.

Conclude with `Fin.card_Iio y`. Repeatedly rewrite using `[this]`. Conclude with `Fin.sum_univ_eq_sum_range (fun i => i) n`.
-/
theorem card_UT (n : ℕ) : Fintype.card (UT n) = ∑ i ∈ range n, i := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp_rw [← Finset.card_filter]
  have : ∀ y : Fin n, (univ.filter (fun x : Fin n => x < y)).card = (y : ℕ) := by
    intro y
    rw [show univ.filter (fun x : Fin n => x < y) = Finset.Iio y by ext; simp]
    exact Fin.card_Iio y
  simp_rw [this]
  exact Fin.sum_univ_eq_sum_range (fun i => i) n

end Formalism.FourierDecayAlt.P.G1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1

/- English proof (translation)
Introduce `n D' x hx`. Establish `hQ : ∀ k, (∏ j ∈ univ \ {k}, x j) ≠ 0` using `fun k => Finset.prod_ne_zero_iff.mpr (fun j _ => hx j)`. Prove the components needed by the constructor for the conclusion. Introduce `k`. Rewrite using `[show (fun ξ => g0 D' (Function.update x k ξ)) = fun ξ => ξ + ∑ j ∈ univ \ {k}, x j + D' / (ξ * ∏ j ∈ univ \ {k}, x j) from funext (phase_function_update D' x k)]`.

Establish `h` using `((hasDerivAt_id' (x k)).add_const (∑ j ∈ univ \ {k}, x j)).add (hasDerivAt_inv_lin D' _ (x k) (hx k) (hQ k))`. Use `h.congr_deriv ?_` and prove the remaining obligations. Unfold `dg0`. Rewrite using `[prod_split x k]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i j`. Rewrite using `[show (fun ξ => dg0 D' (Function.update x j ξ) i) = fun ξ => 1 - D' / (ξ * ∏ l ∈ univ \ {j}, x l) / (Function.update x j ξ i) from`. Use function extensionality and compare the values at `(phase_deriv_update D' x j i)]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `only [Function.update_self]`. Establish `h` using `(hasDerivAt_inv_sq D' _ (x i) (hx i) (hQ i)).const_sub 1`. Use `h.congr_deriv ?_` and prove the remaining obligations. Unfold `hess`. Rewrite using `[prod_split x i]`.

Simplify using the standard rewrite rules. Simplify using `only [Function.update_of_ne hij]`. Establish `h` using `((hasDerivAt_inv_lin D' _ (x j) (hx j) (hQ j)).div_const (x i)).const_sub 1`. Use `h.congr_deriv ?_` and prove the remaining obligations. Unfold `hess`.

Rewrite using `[prod_split x j]`. Use `hx i` as an intermediate fact. Use `hx j` as an intermediate fact. Use `hQ j` as an intermediate fact. Simplify using `only [if_neg hij]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem phase_function_deriv : Formalism.FourierDecayAlt.G.PhaseFunctionDeriv := by
  intro n D' x hx
  have hQ : ∀ k, (∏ j ∈ univ \ {k}, x j) ≠ 0 := fun k => Finset.prod_ne_zero_iff.mpr (fun j _ => hx j)
  constructor
  · intro k
    rw [show (fun ξ => g0 D' (Function.update x k ξ)) = fun ξ =>
      ξ + ∑ j ∈ univ \ {k}, x j + D' / (ξ * ∏ j ∈ univ \ {k}, x j) from funext (phase_function_update D' x k)]
    have h := ((hasDerivAt_id' (x k)).add_const (∑ j ∈ univ \ {k}, x j)).add
      (hasDerivAt_inv_lin D' _ (x k) (hx k) (hQ k))
    refine h.congr_deriv ?_
    unfold dg0
    rw [prod_split x k]
    ring
  · intro i j
    rw [show (fun ξ => dg0 D' (Function.update x j ξ) i) = fun ξ =>
      1 - D' / (ξ * ∏ l ∈ univ \ {j}, x l) / (Function.update x j ξ i) from
      funext (phase_deriv_update D' x j i)]
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      have h := (hasDerivAt_inv_sq D' _ (x i) (hx i) (hQ i)).const_sub 1
      refine h.congr_deriv ?_
      unfold hess
      rw [prod_split x i]
      simp
    · simp only [Function.update_of_ne hij]
      have h := ((hasDerivAt_inv_lin D' _ (x j) (hx j) (hQ j)).div_const (x i)).const_sub 1
      refine h.congr_deriv ?_
      unfold hess
      rw [prod_split x j]
      have := hx i; have := hx j; have := hQ j
      simp only [if_neg hij]
      field_simp

/- English proof (translation)
Introduce `m D' hD`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Establish `hP0 : (∏ k, x k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun k _ => hx k)`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `hxk : ∀ k, x k = D' / ∏ k, x k`. Introduce `k`. Establish `h1` using `h k`. Unfold `dg0 at h1`.

Establish `h2 : D' / (∏ k, x k) / x k = 1` using `by linear_combination -h1`. Rewrite `h2` using `[div_eq_one_iff_eq (hx k)]`. Conclude with `h2.symm`. Use `⟨D' / ∏ k, x k, ?_, funext hxk⟩` and prove the remaining obligations. Establish `hprod : (∏ k, x k) = (D' / ∏ k, x k) ^ (m + 1)` using `by conv_lhs => rw [Finset.prod_congr rfl (fun k _ => hxk k)]`.

Simplify using `[div_pow]`. Rewrite using `[pow_succ, ← hprod]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨z, hz, rfl⟩ k`. Establish `hz0 : z ≠ 0` using `hx 0`.

Simplify using `only [dg0, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hz]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `z hz`. Establish `hz0 : z ≠ 0`.

Introduce and unpack `rfl`. Apply `hD` to reduce the goal to its premises. Rewrite using `[← hz]`. Simplify using the standard rewrite rules. Rewrite using `[← hz]`.

Simplify using `[g0]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phase_function_critical_points : Formalism.FourierDecayAlt.G.PhaseFunctionCritical := by
  intro m D' hD
  constructor
  · intro x hx
    have hP0 : (∏ k, x k) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hx k)
    constructor
    · intro h
      have hxk : ∀ k, x k = D' / ∏ k, x k := by
        intro k
        have h1 := h k
        unfold dg0 at h1
        have h2 : D' / (∏ k, x k) / x k = 1 := by linear_combination -h1
        rw [div_eq_one_iff_eq (hx k)] at h2
        exact h2.symm
      refine ⟨D' / ∏ k, x k, ?_, funext hxk⟩
      have hprod : (∏ k, x k) = (D' / ∏ k, x k) ^ (m + 1) := by
        conv_lhs => rw [Finset.prod_congr rfl (fun k _ => hxk k)]
        simp [div_pow]
      rw [pow_succ, ← hprod]
      field_simp
    · rintro ⟨z, hz, rfl⟩ k
      have hz0 : z ≠ 0 := hx 0
      simp only [dg0, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hz]
      field_simp
      ring
  · intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      apply hD
      rw [← hz]; simp
    rw [← hz]
    simp [g0]; field_simp; ring

/- English proof (translation)
Introduce `m z hz`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[hess]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hess, h]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessian_at_critical : Formalism.FourierDecayAlt.G.HessCrit := by
  intro m z hz
  ext i j
  by_cases h : i = j
  · subst h; simp [hess]; field_simp; ring
  · simp [hess, h]; field_simp; ring

/- English proof (translation)
Introduce `m z`. Rewrite using `[Matrix.det_smul, Fintype.card_fin]`. Establish `hJ : (Matrix.of fun _ _ => (1 : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = Matrix.replicateCol Unit (fun _ => (1 : ℂ)) * Matrix.replicateRow Unit (fun _ => (1 : ℂ))`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.

Rewrite using `[hJ, Matrix.det_one_add_replicateCol_mul_replicateRow]`. Simplify using `[dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessian_determinant : Formalism.FourierDecayAlt.G.HessDet := by
  intro m z
  rw [Matrix.det_smul, Fintype.card_fin]
  have hJ : (Matrix.of fun _ _ => (1 : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      Matrix.replicateCol Unit (fun _ => (1 : ℂ)) * Matrix.replicateRow Unit (fun _ => (1 : ℂ)) := by
    ext i j; simp [Matrix.mul_apply]
  rw [hJ, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨6, fun m D' hD x hx η hη hη' h => gradSmall6 m D' hD x hx η hη hη' h⟩`.
-/
theorem gradient_small_near_critical : Formalism.FourierDecayAlt.G.GradSmall :=
  ⟨6, fun m D' hD x hx η hη hη' h => gradSmall6 m D' hD x hx η hη hη' h⟩

/- English proof (translation)
Introduce `m Kc hK h0 δ hδ`. Take `⟨R, hR⟩` from `hK.isBounded.exists_norm_le`. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `hR1 : (1 : ℝ) ≤ max 1 R` using `le_max_left _ _`. Establish `hc1 : (0 : ℝ) < 1 / (4 * ((m : ℝ) + 2))` using `by positivity`.

Establish `hc2 : (0 : ℝ) < δ / (12 * max 1 R)` using `by positivity`. Use `⟨min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)), lt_min hc1 hc2, ?_⟩` and prove the remaining obligations. Introduce `D' hD x hx hfar`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `hD0 : D' ≠ 0` using `fun h => h0 (h ▸ hD)`. Take `⟨z, hz, hzx⟩` from `gradSmall6 m D' hD0 x hx _ (lt_min hc1 hc2) (min_le_left _ _) hcon`. Establish `hzn : ‖z‖ ≤ max 1 R`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Establish `h1 : 1 ≤ ‖z‖` using `hR1.trans hlt.le`. Establish `h2 : ‖z‖ ≤ ‖z‖ ^ (m + 2)` using `le_self_pow₀ h1 (by omega)`. Rewrite `h2` using `[← norm_pow, hz]`. Establish `h3` using `hR D' hD`. Establish `h4 : R ≤ max 1 R` using `le_max_right _ _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : ‖x - fun _ => z‖ ≤ δ / 2`. Rewrite using `[pi_norm_le_iff_of_nonneg (by linarith)]`. Introduce `k`. Simplify using `only [Pi.sub_apply]`.

Use `(hzx k).trans ?_` and prove the remaining obligations. Establish `h5 : min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)) ≤ δ / (12 * max 1 R)` using `min_le_right _ _`. Establish `h6 : 0 < min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R))` using `lt_min hc1 hc2`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul _ hzn (norm_nonneg _) (by positivity)` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = δ / 2 := by field_simp; norm_num`. Use `hfar z hz` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gradient_lower_bound : Formalism.FourierDecayAlt.G.GradLower := by
  intro m Kc hK h0 δ hδ
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hR1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
  have hc1 : (0 : ℝ) < 1 / (4 * ((m : ℝ) + 2)) := by positivity
  have hc2 : (0 : ℝ) < δ / (12 * max 1 R) := by positivity
  refine ⟨min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)), lt_min hc1 hc2, ?_⟩
  intro D' hD x hx hfar
  by_contra hcon
  push Not at hcon
  have hD0 : D' ≠ 0 := fun h => h0 (h ▸ hD)
  obtain ⟨z, hz, hzx⟩ := gradSmall6 m D' hD0 x hx _ (lt_min hc1 hc2) (min_le_left _ _) hcon
  have hzn : ‖z‖ ≤ max 1 R := by
    by_contra hlt
    push Not at hlt
    have h1 : 1 ≤ ‖z‖ := hR1.trans hlt.le
    have h2 : ‖z‖ ≤ ‖z‖ ^ (m + 2) := le_self_pow₀ h1 (by omega)
    rw [← norm_pow, hz] at h2
    have h3 := hR D' hD
    have h4 : R ≤ max 1 R := le_max_right _ _
    linarith
  have hle : ‖x - fun _ => z‖ ≤ δ / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro k
    simp only [Pi.sub_apply]
    refine (hzx k).trans ?_
    have h5 : min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)) ≤ δ / (12 * max 1 R) := min_le_right _ _
    have h6 : 0 < min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)) := lt_min hc1 hc2
    calc 6 * min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)) * ‖z‖
        ≤ 6 * (δ / (12 * max 1 R)) * max 1 R := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          linarith
      _ = δ / 2 := by field_simp; norm_num
  have := hfar z hz
  linarith

/- English proof (translation)
Introduce `s a hs`. Prove the components needed by the constructor for the conclusion. Introduce `z`. Simplify using `[rootSet, Polynomial.mem_nthRoots hs]`. Introduce `ha`.

Establish `hprim` using `Complex.isPrimitiveRoot_exp s hs.ne'`. Unfold `rootSet`. Rewrite using `[Multiset.toFinset_card_of_nodup (hprim.nthRoots_nodup ha), hprim.card_nthRoots]`. Rewrite using `[if_pos (IsAlgClosed.exists_pow_nat_eq a hs)]`.
-/
theorem root_set_characterization : Formalism.FourierDecayAlt.G.RootSetSpec := by
  intro s a hs
  constructor
  · intro z
    simp [rootSet, Polynomial.mem_nthRoots hs]
  · intro ha
    have hprim := Complex.isPrimitiveRoot_exp s hs.ne'
    unfold rootSet
    rw [Multiset.toFinset_card_of_nodup (hprim.nthRoots_nodup ha), hprim.card_nthRoots]
    rw [if_pos (IsAlgClosed.exists_pow_nat_eq a hs)]

/- English proof (translation)
Introduce `m τ ζ hτ hζ`. Establish `h1 : τ ^ ((m + 1) * (m + 2)) = τ ^ ((m + 1) ^ 2) * τ ^ (m + 1)` using `by rw [← pow_add]; congr 1; ring`. Establish `h2 : ζ ^ ((m + 2) * (m + 1)) * ζ ^ (m + 1) = ζ ^ ((m + 1) ^ 2) * ζ ^ (2 * (m + 1))`. Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hm : ((m : ℝ) + 2) ≠ 0` using `by positivity`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts. Combine the linear relations using `[h2]`.
-/
theorem stationary_leading_constant : Formalism.FourierDecayAlt.G.LeadingConstant := by
  intro m τ ζ hτ hζ
  have h1 : τ ^ ((m + 1) * (m + 2)) = τ ^ ((m + 1) ^ 2) * τ ^ (m + 1) := by rw [← pow_add]; congr 1; ring
  have h2 : ζ ^ ((m + 2) * (m + 1)) * ζ ^ (m + 1) = ζ ^ ((m + 1) ^ 2) * ζ ^ (2 * (m + 1)) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
  rw [h1]; field_simp; linarith [h2]

/- English proof (translation)
Introduce `n`. Prove the components needed by the constructor for the conclusion. Rewrite using `[card_UT, mul_comm]`. Conclude with `Finset.sum_range_id_mul_two n`. Rewrite using `[card_UT, card_UT, Finset.sum_range_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dimension_count : Formalism.FourierDecayAlt.G.DimCount := by
  intro n
  constructor
  · rw [card_UT, mul_comm]; exact Finset.sum_range_id_mul_two n
  · rw [card_UT, card_UT, Finset.sum_range_succ]; ring

end Formalism.FourierDecayAlt.P
