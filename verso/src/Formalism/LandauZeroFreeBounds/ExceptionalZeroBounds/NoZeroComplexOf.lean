import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hre : ρ.re < 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ`. Establish `hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re` using `by simp`.

Establish `hwpos : 0 < ((σ : ℂ) + t * I - ρ).re` using `by rw [hwre]; linarith`. Establish `hw0 : (σ : ℂ) + t * I - ρ ≠ 0` using `fun h => by rw [h] at hwpos; simp at hwpos`. Rewrite using `[one_div, Complex.inv_re]`. Conclude with `div_pos hwpos (Complex.normSq_pos.mpr hw0)`.
-/
lemma re_one_div_sub_zero_pos_ter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + t * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ
  have hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
  have hwpos : 0 < ((σ : ℂ) + t * I - ρ).re := by rw [hwre]; linarith
  have hw0 : (σ : ℂ) + t * I - ρ ≠ 0 := fun h => by rw [h] at hwpos; simp at hwpos
  rw [one_div, Complex.inv_re]
  exact div_pos hwpos (Complex.normSq_pos.mpr hw0)

/- English proof (translation)
Conclude with `Finset.sum_nonneg fun ρ hρ => mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_ter χ hχ ρ (hZ ρ hρ) σ t hσ).le`.
-/
lemma sum_mult_re_one_div_sub_zeros_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + t * I - ρ)).re := by
  exact Finset.sum_nonneg fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_ter χ hχ ρ (hZ ρ hρ) σ t hσ).le

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Unfold `NoZeroComplexOf LocalZeros LLogDerivRight Positivity NoZeroComplex InRegion`. Introduce `hLZ hLD hPos`. Take `⟨C0, hC0⟩` from `hLZ`. Take `⟨C1, hC1nn, hC1⟩` from `hLD`. Use `set K : ℝ := |C0| with hK`.

Establish `hKnn : 0 ≤ K` using `abs_nonneg _`. Use `set A : ℝ := 6 * K + 5 * C1 + 1 with hA`. Establish `hApos : 0 < A` using `by rw [hA]; linarith`. Use `set δ : ℝ := min (1 / 10) (1 / (2 * A)) with hδ`. Establish `hδpos : 0 < δ` using `lt_min (by norm_num) (by positivity)`.

Establish `hδ1 : δ ≤ 1 / 10` using `min_le_left _ _`. Establish `hδ2 : δ ≤ 1 / (2 * A)` using `min_le_right _ _`. Use `⟨δ / 8, by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ s hχ2 hreg hzero`. Establish `hχ : χ ≠ 1` using `fun h => hχ2 (by rw [h, one_pow])`.

Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Use `set ℓ := Real.log ((q : ℝ) * (|s.im| + 2)) with hℓ`. Establish `hlog2 : Real.log 2 ≤ ℓ` using `Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])`. Establish `hl2 : (0.69 : ℝ) < Real.log 2`. Use `Real.log_two_gt_d9` as an intermediate fact.

Evaluate the numerical expressions using `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hℓ69 : (0.69 : ℝ) < ℓ` using `lt_of_lt_of_le hl2 hlog2`. Establish `hℓpos : 0 < ℓ` using `by linarith`. Establish `hβ1 : s.re < 1`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hzero`. Establish `hsmall : δ / 8 / ℓ ≤ 1 / 10`. Rewrite using `[div_le_iff₀ hℓpos]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hβ9 : 9 / 10 ≤ s.re` using `by linarith`. Use `set σ : ℝ := 1 + δ / ℓ with hσ`. Establish `hvpos : 0 < δ / ℓ` using `div_pos hδpos hℓpos`. Establish `hσ1 : 1 < σ` using `by linarith`.

Establish `hσ2 : σ ≤ 6 / 5`. Establish `: δ / ℓ ≤ 1 / 5`. Rewrite using `[div_le_iff₀ hℓpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set u : ℝ := 1 / δ with hu`. Establish `b0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ ℓ * u + C1`. Establish `h1` using `hC1 q 1 (σ : ℂ) (by simpa using hσ1)`. Establish `h2` using `Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ))`. Establish `h3 : 1 / ((σ : ℂ).re - 1) = ℓ * u`.

Rewrite using `[Complex.ofReal_re, hσ, hu, add_sub_cancel_left, one_div_div, div_eq_mul_one_div]`. Rewrite `h1` using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨Z, m, hZ, hm1, -, hbd⟩` from `hC0 q χ hχ s.im`. Establish `hsZ : s ∈ Z`.

Use `(hZ s).mpr ⟨?_, hzero⟩` and prove the remaining obligations. Establish `e : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[mem_closedBall_iff_norm, e, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`.

Establish `hterm : 1 / (σ - s.re) ≤ (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re`. Establish `e : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `e2 : (1 / ((σ - s.re : ℝ) : ℂ)).re = 1 / (σ - s.re)`. Rewrite using `[← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]`.

Rewrite using `[e, e2]`. Establish `hm : (1 : ℝ) ≤ (m s : ℝ)` using `by exact_mod_cast hm1 s hsZ`. Establish `hpos : 0 < 1 / (σ - s.re)` using `by apply div_pos one_pos; linarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsum : (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re` using `Finset.single_le_sum (f := fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re) (fun ρ hρ => mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_ter χ hχ ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le) hsZ`.

Establish `hgap : σ - s.re ≤ (9 / 8) * (δ / ℓ)`. Establish `: δ / 8 / ℓ = (δ / ℓ) / 8` using `by ring`. Rewrite using `[hσ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgappos : 0 < σ - s.re` using `by linarith`.

Establish `hinv : (8 / 9) * (ℓ * u) ≤ 1 / (σ - s.re)`. Establish `h1` using `one_div_le_one_div_of_le hgappos hgap`. Establish `h2 : 1 / ((9 / 8) * (δ / ℓ)) = (8 / 9) * (ℓ * u)`. Rewrite using `[hu]`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `b1 : (negLD χ ((σ : ℂ) + s.im * I)).re ≤ K * ℓ - (8 / 9) * (ℓ * u)`. Establish `h1` using `hbd σ hσ1 hσ2`. Rewrite `h1` using `[← hℓ]`. Establish `h2 : C0 * ℓ ≤ K * ℓ` using `mul_le_mul_of_nonneg_right (le_abs_self C0) hℓpos.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨Z2, m2, hZ2, -, -, hbd2⟩` from `hC0 q (χ ^ 2) hχ2 (2 * s.im)`. Establish `hL2 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * ℓ`. Establish `ha` using `abs_nonneg s.im`. Establish `h1 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ Real.log (((q : ℝ) * (|s.im| + 2)) ^ 2)`.

Apply `Real.log_le_log` to reduce the goal to its premises. Rewrite using `[abs_mul, abs_two]`. Check the signs of the components of the expression. Rewrite using `[abs_mul, abs_two]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hq (sq_nonneg (|s.im| + 2))]`.

Rewrite `h1` using `[Real.log_pow]`. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL2nn : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2))` using `Real.log_nonneg (by nlinarith [abs_nonneg (2 * s.im)])`. Establish `b2 : (negLD (χ ^ 2) ((σ : ℂ) + 2 * s.im * I)).re ≤ 2 * (K * ℓ)`.

Establish `h1` using `hbd2 σ hσ1 hσ2`. Move the coercions through the operations in `at h1`. Establish `h2` using `sum_mult_re_one_div_sub_zeros_nonneg (χ ^ 2) hχ2 Z2 m2 (fun ρ hρ => ((hZ2 ρ).mp hρ).2) σ (2 * s.im) hσ1`. Move the coercions through the operations in `at h2`. Establish `h3 : C0 * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * Real.log ((q : ℝ) * (|2 * s.im| + 2))` using `mul_le_mul_of_nonneg_right (le_abs_self C0) hL2nn`.

Establish `h4 : K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * (2 * ℓ)` using `mul_le_mul_of_nonneg_left hL2 hKnn`. Establish `h5 : K * (2 * ℓ) = 2 * (K * ℓ)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP` using `(hPos q σ hσ1).1 χ s.im`. Establish `hu2 : 2 * A ≤ u`.

Establish `h1` using `one_div_le_one_div_of_le hδpos hδ2`. Rewrite `h1` using `[one_div_one_div]`. Conclude with `h1`. Establish `cu : 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ ≤ ℓ * u`. Establish `h1` using `mul_le_mul_of_nonneg_left hu2 hℓpos.le`.

Establish `e : ℓ * (2 * A) = 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ` using `by rw [hA]; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `c1 : 3 * C1 ≤ 5 * (C1 * ℓ)`. Use `mul_le_mul_of_nonneg_left hℓ69.le hC1nn` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hKl : 0 ≤ K * ℓ` using `mul_nonneg hKnn hℓpos.le`. Establish `hCl : 0 ≤ C1 * ℓ` using `mul_nonneg hC1nn hℓpos.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zeroFreeNonRealCharOfBounds : NoZeroComplexOf := by
  unfold NoZeroComplexOf LocalZeros LLogDerivRight Positivity NoZeroComplex InRegion
  intro hLZ hLD hPos
  obtain ⟨C0, hC0⟩ := hLZ
  obtain ⟨C1, hC1nn, hC1⟩ := hLD
  set K : ℝ := |C0| with hK
  have hKnn : 0 ≤ K := abs_nonneg _
  set A : ℝ := 6 * K + 5 * C1 + 1 with hA
  have hApos : 0 < A := by rw [hA]; linarith
  set δ : ℝ := min (1 / 10) (1 / (2 * A)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 10 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (2 * A) := min_le_right _ _
  refine ⟨δ / 8, by positivity, ?_⟩
  intro q _ χ s hχ2 hreg hzero
  have hχ : χ ≠ 1 := fun h => hχ2 (by rw [h, one_pow])
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log ((q : ℝ) * (|s.im| + 2)) with hℓ
  have hlog2 : Real.log 2 ≤ ℓ :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hℓ69 : (0.69 : ℝ) < ℓ := lt_of_lt_of_le hl2 hlog2
  have hℓpos : 0 < ℓ := by linarith
  have hβ1 : s.re < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hzero
  have hsmall : δ / 8 / ℓ ≤ 1 / 10 := by
    rw [div_le_iff₀ hℓpos]
    linarith
  have hβ9 : 9 / 10 ≤ s.re := by linarith
  set σ : ℝ := 1 + δ / ℓ with hσ
  have hvpos : 0 < δ / ℓ := div_pos hδpos hℓpos
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : δ / ℓ ≤ 1 / 5 := by
      rw [div_le_iff₀ hℓpos]
      linarith
    linarith
  set u : ℝ := 1 / δ with hu

  have b0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ ℓ * u + C1 := by
    have h1 := hC1 q 1 (σ : ℂ) (by simpa using hσ1)
    have h2 := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ))
    have h3 : 1 / ((σ : ℂ).re - 1) = ℓ * u := by
      rw [Complex.ofReal_re, hσ, hu, add_sub_cancel_left, one_div_div, div_eq_mul_one_div]
    rw [h3] at h1
    linarith

  obtain ⟨Z, m, hZ, hm1, -, hbd⟩ := hC0 q χ hχ s.im
  have hsZ : s ∈ Z := by
    refine (hZ s).mpr ⟨?_, hzero⟩
    have e : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [mem_closedBall_iff_norm, e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hterm : 1 / (σ - s.re) ≤ (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re := by
    have e : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have e2 : (1 / ((σ - s.re : ℝ) : ℂ)).re = 1 / (σ - s.re) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [e, e2]
    have hm : (1 : ℝ) ≤ (m s : ℝ) := by exact_mod_cast hm1 s hsZ
    have hpos : 0 < 1 / (σ - s.re) := by apply div_pos one_pos; linarith
    nlinarith
  have hsum : (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re ≤
      ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re :=
    Finset.single_le_sum (f := fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re)
      (fun ρ hρ => mul_nonneg (Nat.cast_nonneg _)
        (re_one_div_sub_zero_pos_ter χ hχ ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le) hsZ
  have hgap : σ - s.re ≤ (9 / 8) * (δ / ℓ) := by
    have : δ / 8 / ℓ = (δ / ℓ) / 8 := by ring
    rw [hσ]
    linarith
  have hgappos : 0 < σ - s.re := by linarith
  have hinv : (8 / 9) * (ℓ * u) ≤ 1 / (σ - s.re) := by
    have h1 := one_div_le_one_div_of_le hgappos hgap
    have h2 : 1 / ((9 / 8) * (δ / ℓ)) = (8 / 9) * (ℓ * u) := by
      rw [hu]
      field_simp
    linarith
  have b1 : (negLD χ ((σ : ℂ) + s.im * I)).re ≤ K * ℓ - (8 / 9) * (ℓ * u) := by
    have h1 := hbd σ hσ1 hσ2
    rw [← hℓ] at h1
    have h2 : C0 * ℓ ≤ K * ℓ := mul_le_mul_of_nonneg_right (le_abs_self C0) hℓpos.le
    linarith

  obtain ⟨Z2, m2, hZ2, -, -, hbd2⟩ := hC0 q (χ ^ 2) hχ2 (2 * s.im)
  have hL2 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * ℓ := by
    have ha := abs_nonneg s.im
    have h1 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ Real.log (((q : ℝ) * (|s.im| + 2)) ^ 2) := by
      apply Real.log_le_log
      · rw [abs_mul, abs_two]
        positivity
      · rw [abs_mul, abs_two]
        nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg (|s.im| + 2))]
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hL2nn : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg (2 * s.im)])
  have b2 : (negLD (χ ^ 2) ((σ : ℂ) + 2 * s.im * I)).re ≤ 2 * (K * ℓ) := by
    have h1 := hbd2 σ hσ1 hσ2
    push_cast at h1
    have h2 := sum_mult_re_one_div_sub_zeros_nonneg (χ ^ 2) hχ2 Z2 m2 (fun ρ hρ => ((hZ2 ρ).mp hρ).2) σ (2 * s.im) hσ1
    push_cast at h2
    have h3 : C0 * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C0) hL2nn
    have h4 : K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * (2 * ℓ) :=
      mul_le_mul_of_nonneg_left hL2 hKnn
    have h5 : K * (2 * ℓ) = 2 * (K * ℓ) := by ring
    linarith

  have hP := (hPos q σ hσ1).1 χ s.im
  have hu2 : 2 * A ≤ u := by
    have h1 := one_div_le_one_div_of_le hδpos hδ2
    rw [one_div_one_div] at h1
    exact h1
  have cu : 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ ≤ ℓ * u := by
    have h1 := mul_le_mul_of_nonneg_left hu2 hℓpos.le
    have e : ℓ * (2 * A) = 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ := by rw [hA]; ring
    linarith
  have c1 : 3 * C1 ≤ 5 * (C1 * ℓ) := by
    have := mul_le_mul_of_nonneg_left hℓ69.le hC1nn
    linarith
  have hKl : 0 ≤ K * ℓ := mul_nonneg hKnn hℓpos.le
  have hCl : 0 ≤ C1 * ℓ := mul_nonneg hC1nn hℓpos.le
  linarith

end Formalism.ZeroFreeDirichlet
