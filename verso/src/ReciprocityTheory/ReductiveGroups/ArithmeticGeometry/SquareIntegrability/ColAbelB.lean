import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound

namespace ReciprocityTheory.ChartRestriction.G.I2

section

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

def cabPoly (η : EuclideanSpace ℂ ι) (c : ℕ) : MvPolynomial ι ℂ :=
  (∑ i, MvPolynomial.C ((starRingEnd ℂ) (η i)) * MvPolynomial.X i) ^ c

/- English proof (translation)
Unfold `cabPoly`. Use `(MvPolynomial.totalDegree_pow _ _).trans ?_` and prove the remaining obligations. Establish `: (∑ i, MvPolynomial.C ((starRingEnd ℂ) (η i)) * MvPolynomial.X i : MvPolynomial ι ℂ).totalDegree ≤ 1`. Use `(MvPolynomial.totalDegree_finsetSum _ _).trans ?_` and prove the remaining obligations. Use `Finset.sup_le fun i _ => ?_` and prove the remaining obligations.

Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Simplify using `[MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cabPoly_deg (η : EuclideanSpace ℂ ι) (c : ℕ) : (cabPoly η c).totalDegree ≤ c := by
  unfold cabPoly
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  have : (∑ i, MvPolynomial.C ((starRingEnd ℂ) (η i)) * MvPolynomial.X i : MvPolynomial ι ℂ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun i _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  calc c * _ ≤ c * 1 := Nat.mul_le_mul_left c this
    _ = c := mul_one c

/- English proof (translation)
Unfold `cabPoly Hf`. Simplify using `[mul_comm]`.
-/
theorem cabPoly_eval (η v : EuclideanSpace ℂ ι) (c : ℕ) :
    MvPolynomial.eval (fun i => v i) (cabPoly η c) = (Hf v η) ^ c := by
  unfold cabPoly Hf
  simp [mul_comm]

/- English proof (translation)
Establish `: Hf v η = inner ℂ η v`. Unfold `Hf`. Simplify using `[PiLp.inner_apply]`. Rewrite using `[this, mul_comm]`. Conclude with `norm_inner_le_norm _ _`.
-/
theorem cab_Hf_norm_le (v η : EuclideanSpace ℂ ι) : ‖Hf v η‖ ≤ ‖v‖ * ‖η‖ := by
  have : Hf v η = inner ℂ η v := by
    unfold Hf; simp [PiLp.inner_apply]
  rw [this, mul_comm]
  exact norm_inner_le_norm _ _

/- English proof (translation)
Rewrite using `[← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex, finrank_euclideanSpace]`.
-/
theorem cab_finrank : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
    finrank_euclideanSpace]

/- English proof (translation)
Establish `hq' : (0 : ℝ) < q` using `by exact_mod_cast hq`. Use `set s : ℝ := q * Real.pi / 2 with hs`. Establish `hs0 : 0 < s` using `by positivity`. Establish `hpt : ∀ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) (cabPoly η c)‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ (c.factorial * (2 / (q * Real.pi)) ^ c) * Real.exp (-s * ‖v‖ ^ 2)`. Introduce `v`.

Rewrite using `[cabPoly_eval, norm_pow]`. Establish `h1 : ‖Hf v η‖ ≤ ‖v‖` using `(cab_Hf_norm_le v η).trans (mul_le_of_le_one_right (norm_nonneg _) hη)`. Establish `h2 : (‖Hf v η‖ ^ c) ^ 2 ≤ (‖v‖ ^ 2) ^ c`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h1 _`.

Establish `h3 : (s * ‖v‖ ^ 2) ^ c / c.factorial ≤ Real.exp (s * ‖v‖ ^ 2)` using `Real.pow_div_factorial_le_exp (x := s * ‖v‖ ^ 2) (hx := by positivity) (n := c)`. Establish `hf : (0 : ℝ) < c.factorial` using `by exact_mod_cast Nat.factorial_pos c`. Establish `h4 : (‖v‖ ^ 2) ^ c ≤ c.factorial * (1 / s) ^ c * Real.exp (s * ‖v‖ ^ 2)`. Rewrite `h3` using `[div_le_iff₀ hf, mul_pow]`. Establish `: (‖v‖ ^ 2) ^ c = (s ^ c * (‖v‖ ^ 2) ^ c) * (1 / s) ^ c`.

Rewrite using `[mul_comm (s ^ c), mul_assoc, ← mul_pow, mul_one_div_cancel hs0.ne', one_pow, mul_one]`. Rewrite using `[this]`. Establish `hp : 0 ≤ (1 / s) ^ c` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : 1 / s = 2 / (q * Real.pi)` using `by rw [hs]; field_simp`.

Rewrite `h4` using `[h5]`. Establish `he : Real.exp (s * ‖v‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) = Real.exp (-s * ‖v‖ ^ 2)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Rewrite using `[hs]`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Establish `hint : Integrable (fun v : EuclideanSpace ℂ ι => (c.factorial * (2 / (q * Real.pi)) ^ c) * Real.exp (-s * ‖v‖ ^ 2))` using `(pa_gauss_integrable hs0).const_mul _`. Use `(integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity) hint (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hs0, cab_finrank]`.

Use `congr 1`. Establish `: Real.pi / s = 2 / q` using `by rw [hs]; field_simp`. Rewrite using `[this]`. Establish `: ((2 * Fintype.card ι : ℕ) : ℝ) / 2 = (Fintype.card ι : ℝ)` using `by push_cast; ring`. Rewrite using `[this, Real.rpow_natCast]`.
-/
theorem cab_J_le (η : EuclideanSpace ℂ ι) (hη : ‖η‖ ≤ 1) (c q : ℕ) (hq : 1 ≤ q) :
    ∫ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) (cabPoly η c)‖ ^ 2 *
      Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤
      c.factorial * (2 / (q * Real.pi)) ^ c * (2 / q) ^ Fintype.card ι := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set s : ℝ := q * Real.pi / 2 with hs
  have hs0 : 0 < s := by positivity
  have hpt : ∀ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) (cabPoly η c)‖ ^ 2 *
      Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤
      (c.factorial * (2 / (q * Real.pi)) ^ c) * Real.exp (-s * ‖v‖ ^ 2) := by
    intro v
    rw [cabPoly_eval, norm_pow]
    have h1 : ‖Hf v η‖ ≤ ‖v‖ := (cab_Hf_norm_le v η).trans (mul_le_of_le_one_right (norm_nonneg _) hη)
    have h2 : (‖Hf v η‖ ^ c) ^ 2 ≤ (‖v‖ ^ 2) ^ c := by
      rw [← pow_mul, ← pow_mul, mul_comm]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 _
    have h3 : (s * ‖v‖ ^ 2) ^ c / c.factorial ≤ Real.exp (s * ‖v‖ ^ 2) :=
      Real.pow_div_factorial_le_exp (x := s * ‖v‖ ^ 2) (hx := by positivity) (n := c)
    have hf : (0 : ℝ) < c.factorial := by exact_mod_cast Nat.factorial_pos c
    have h4 : (‖v‖ ^ 2) ^ c ≤ c.factorial * (1 / s) ^ c * Real.exp (s * ‖v‖ ^ 2) := by
      rw [div_le_iff₀ hf, mul_pow] at h3
      have : (‖v‖ ^ 2) ^ c = (s ^ c * (‖v‖ ^ 2) ^ c) * (1 / s) ^ c := by
        rw [mul_comm (s ^ c), mul_assoc, ← mul_pow, mul_one_div_cancel hs0.ne', one_pow, mul_one]
      rw [this]
      have hp : 0 ≤ (1 / s) ^ c := by positivity
      calc s ^ c * (‖v‖ ^ 2) ^ c * (1 / s) ^ c ≤ Real.exp (s * ‖v‖ ^ 2) * c.factorial * (1 / s) ^ c :=
            mul_le_mul_of_nonneg_right h3 hp
        _ = _ := by ring
    have h5 : 1 / s = 2 / (q * Real.pi) := by rw [hs]; field_simp
    rw [h5] at h4
    have he : Real.exp (s * ‖v‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) = Real.exp (-s * ‖v‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; rw [hs]; ring
    calc (‖Hf v η‖ ^ c) ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)
        ≤ (c.factorial * (2 / (q * Real.pi)) ^ c * Real.exp (s * ‖v‖ ^ 2)) *
          Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (h2.trans h4) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, he]
  have hint : Integrable (fun v : EuclideanSpace ℂ ι =>
      (c.factorial * (2 / (q * Real.pi)) ^ c) * Real.exp (-s * ‖v‖ ^ 2)) :=
    (pa_gauss_integrable hs0).const_mul _
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity) hint
    (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hs0, cab_finrank]
  congr 1
  have : Real.pi / s = 2 / q := by rw [hs]; field_simp
  rw [this]
  have : ((2 * Fintype.card ι : ℕ) : ℝ) / 2 = (Fintype.card ι : ℝ) := by push_cast; ring
  rw [this, Real.rpow_natCast]

end

end

section

open MeasureTheory

noncomputable section

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `hs : 0 < Real.sqrt (q * Real.pi)`. Apply `Real.sqrt_pos.mpr; have : (1 : ℝ) ≤ q := by exact_mod_cast hq` to reduce the goal to its premises. Check the signs of the components of the expression. Establish `hcard : 0 < 2 * Fintype.card ι` using `by have := Fintype.card_pos (α := ι); omega`. Establish `hmem : ∃ t, t ∈ {t : ℝ | ∃ x ∈ lat Y.b, x ≠ 0 ∧ t = ‖x‖}`.

Use `⟨‖Y.b ⟨0, hcard⟩‖, Y.b ⟨0, hcard⟩, Submodule.subset_span ⟨_, rfl⟩, Y.b.ne_zero _, rfl⟩` and prove the remaining obligations. Rewrite using `[← div_le_iff₀' hs]`. Unfold `GT.la1`. Apply `le_csInf hmem` to reduce the goal to its premises. Introduce and unpack `t ⟨x, hx, hx0, rfl⟩`.

Rewrite using `[div_le_iff₀' hs]`. Conclude with `hlat x hx hx0`.
-/
theorem sqrt_pi_mul_firstMinimum_ge (Y : GT ι) (q : ℕ) (R0 : ℝ) (hq : 1 ≤ q) (hne : Nonempty ι)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) :
    R0 ≤ Real.sqrt (q * Real.pi) * Y.la1 := by
  have hs : 0 < Real.sqrt (q * Real.pi) := by
    apply Real.sqrt_pos.mpr; have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    positivity
  have hcard : 0 < 2 * Fintype.card ι := by have := Fintype.card_pos (α := ι); omega
  have hmem : ∃ t, t ∈ {t : ℝ | ∃ x ∈ lat Y.b, x ≠ 0 ∧ t = ‖x‖} := by
    refine ⟨‖Y.b ⟨0, hcard⟩‖, Y.b ⟨0, hcard⟩, Submodule.subset_span ⟨_, rfl⟩, Y.b.ne_zero _, rfl⟩
  rw [← div_le_iff₀' hs]
  unfold GT.la1
  apply le_csInf hmem
  rintro t ⟨x, hx, hx0, rfl⟩
  rw [div_le_iff₀' hs]
  exact hlat x hx hx0

/- English proof (translation)
Establish `hq1 : 1 ≤ q` using `by omega`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast (by omega : 0 < q)`. Establish `h` using `hS ι Y q hq1 β hβ w`. Use `set G := Fintype.card ι with hG`. Use `set A := 4 * Real.sqrt (2 * G) / (Real.sqrt (q * Real.pi) * Y.la1) with hA`.

Establish `hA2 : (1 + A) ^ 2 ≤ 2.56`. Break down `Nat.eq_zero_or_pos G with h0 | h0` into its components or cases. Rewrite using `[hA, h0]`. Simplify using the standard rewrite rules. Evaluate the numerical expressions.

Establish `hne : Nonempty ι` using `Fintype.card_pos_iff.mp h0`. Establish `hla` using `sqrt_pi_mul_firstMinimum_ge Y q R0 hq1 hne hlat`. Establish `hlap : 0 < Real.sqrt (q * Real.pi) * Y.la1` using `lt_of_lt_of_le hR0 hla`. Establish `hA0 : 0 ≤ A` using `by rw [hA]; positivity`. Establish `hAle : A ≤ 4 * Real.sqrt (2 * G) / R0`.

Rewrite using `[hA]; exact div_le_div_of_nonneg_left (by positivity) hR0 hla`. Establish `hsq : (4 * Real.sqrt (2 * G) / R0) ^ 2 ≤ 0.36`. Rewrite using `[div_pow, mul_pow, Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `: A ≤ 0.6`.

Establish `h1 : A ^ 2 ≤ 0.36` using `le_trans (pow_le_pow_left₀ hA0 hAle 2) hsq`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `hpow : (1 + A) ^ (2 * G) ≤ 2.56 ^ G`. Rewrite using `[pow_mul]; exact pow_le_pow_left₀ (by positivity) hA2 G`.

Establish `hl0 : 0 ≤ Y.l2 q β`. Unfold `GT.l2`. Rewrite using `[MeasureTheory.setAverage_eq]`. Conclude with `smul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg) (MeasureTheory.integral_nonneg fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)`. Establish `hqG : (0 : ℝ) ≤ 2 * (q : ℝ) ^ G` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c := by`. Use `congr 3`.

Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions.
-/
theorem cab_sup (hS : GSupStatement) (Y : GT ι) (q c : ℕ) (hq : 2 ≤ q) (R0 : ℝ) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (h90 : 90 * (Fintype.card ι : ℝ) ≤ R0 ^ 2) (β : EuclideanSpace ℂ ι → ℂ) (hβ : β ∈ Y.Sec q)
    (hl2 : Y.l2 q β ≤ 6 * (c.factorial * (2 / (q * Real.pi)) ^ c * (2 / q) ^ Fintype.card ι))
    (w : EuclideanSpace ℂ ι) :
    Y.ptN2 q β w ≤ 12 * (5.12 : ℝ) ^ Fintype.card ι * c.factorial * (2 / (q * Real.pi)) ^ c := by
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h := hS ι Y q hq1 β hβ w
  set G := Fintype.card ι with hG
  set A := 4 * Real.sqrt (2 * G) / (Real.sqrt (q * Real.pi) * Y.la1) with hA
  have hA2 : (1 + A) ^ 2 ≤ 2.56 := by
    rcases Nat.eq_zero_or_pos G with h0 | h0
    · rw [hA, h0]; simp; norm_num
    · have hne : Nonempty ι := Fintype.card_pos_iff.mp h0
      have hla := sqrt_pi_mul_firstMinimum_ge Y q R0 hq1 hne hlat
      have hlap : 0 < Real.sqrt (q * Real.pi) * Y.la1 := lt_of_lt_of_le hR0 hla
      have hA0 : 0 ≤ A := by rw [hA]; positivity
      have hAle : A ≤ 4 * Real.sqrt (2 * G) / R0 := by
        rw [hA]; exact div_le_div_of_nonneg_left (by positivity) hR0 hla
      have hsq : (4 * Real.sqrt (2 * G) / R0) ^ 2 ≤ 0.36 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)]
        nlinarith
      have : A ≤ 0.6 := by
        have h1 : A ^ 2 ≤ 0.36 := le_trans (pow_le_pow_left₀ hA0 hAle 2) hsq
        nlinarith
      nlinarith
  have hpow : (1 + A) ^ (2 * G) ≤ 2.56 ^ G := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hA2 G
  have hl0 : 0 ≤ Y.l2 q β := by
    unfold GT.l2
    rw [MeasureTheory.setAverage_eq]
    exact smul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg)
      (MeasureTheory.integral_nonneg fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hqG : (0 : ℝ) ≤ 2 * (q : ℝ) ^ G := by positivity
  calc Y.ptN2 q β w ≤ 2 * (q : ℝ) ^ G * (1 + A) ^ (2 * G) * Y.l2 q β := h
    _ ≤ 2 * (q : ℝ) ^ G * 2.56 ^ G * (6 * (c.factorial * (2 / (q * Real.pi)) ^ c * (2 / q) ^ G)) := by
        gcongr
    _ = 12 * ((q : ℝ) * (2 / q) * 2.56) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c := by
        rw [mul_pow, mul_pow]; ring
    _ = 12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c := by
        congr 3; field_simp; norm_num

end

end

section

noncomputable section

/- English proof (translation)
Use `Real.quadratic_le_exp_of_nonneg (x := 1 / 4) (by norm_num)` as an intermediate fact. Evaluate the numerical expressions using `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cab_exp_quarter : (1.28 : ℝ) ≤ Real.exp (1 / 4) := by
  have := Real.quadratic_le_exp_of_nonneg (x := 1 / 4) (by norm_num)
  norm_num at this ⊢; linarith

/- English proof (translation)
Establish `hpi` using `Real.pi_gt_d2`. Establish `hpi4` using `Real.pi_lt_d2`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hc : (2 * (c + 1) / Real.pi) ^ c ≤ Real.exp (c * Real.log (q * c))`. Break down `Nat.eq_zero_or_pos c with h0 | h0` into its components or cases.

Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Establish `hc1 : (1 : ℝ) ≤ c` using `by exact_mod_cast h0`. Establish `hqc : 0 < q * c` using `by positivity`. Rewrite using `[Real.exp_nat_mul, Real.exp_log hqc]`.

Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Rewrite using `[div_le_iff₀ Real.pi_pos]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlog : 0 ≤ c * Real.log (q * c)`. Break down `Nat.eq_zero_or_pos c with h0 | h0` into its components or cases.

Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Establish `hc1 : (1 : ℝ) ≤ c` using `by exact_mod_cast h0`. Conclude with `mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith))`. Establish `hg : (5.12 : ℝ) ^ gA ≤ 4 ^ gA * Real.exp (gA / 4)`.

Establish `: (5.12 : ℝ) ^ gA = 4 ^ gA * 1.28 ^ gA` using `by rw [← mul_pow]; norm_num`. Rewrite using `[this]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hexp : Real.exp (gA / 4) * Real.exp (c * Real.log (q * c)) * Real.exp (5 * Real.pi * c) * Real.exp (-((Real.pi - 2) * t0)) ≤ 1`.

Rewrite using `[← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]`. Establish `hcl : (c : ℝ) * Real.log (q * c) = c * Real.log (q * c)` using `rfl`. Establish `hc0 : (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`. Establish `hg0 : (0 : ℝ) ≤ gA` using `Nat.cast_nonneg gA`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hC5 (by linarith : (0 : ℝ) ≤ (Real.pi - 2) / 2), mul_le_mul_of_nonneg_left hC6 (by linarith : (0 : ℝ) ≤ (Real.pi - 2) / 2)]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem cab_key (c gA : ℕ) (q t0 : ℝ) (hq : 2 ≤ q) (dst : ℝ) (hd : 0 ≤ dst)
    (hC5 : 4 * c * (7 + Real.log (q * c)) + dst + 1 ≤ t0) (hC6 : gA * Real.log 2 ≤ t0) :
    (5.12 : ℝ) ^ gA * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
      Real.exp (-((Real.pi - 2) * t0)) ≤ 4 ^ gA := by
  have hpi := Real.pi_gt_d2
  have hpi4 := Real.pi_lt_d2
  have hl2 := Real.log_two_gt_d9

  have hc : (2 * (c + 1) / Real.pi) ^ c ≤ Real.exp (c * Real.log (q * c)) := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp
    · have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast h0
      have hqc : 0 < q * c := by positivity
      rw [Real.exp_nat_mul, Real.exp_log hqc]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ Real.pi_pos]; nlinarith
  have hlog : 0 ≤ c * Real.log (q * c) := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp
    · have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast h0
      exact mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith))
  have hg : (5.12 : ℝ) ^ gA ≤ 4 ^ gA * Real.exp (gA / 4) := by
    have : (5.12 : ℝ) ^ gA = 4 ^ gA * 1.28 ^ gA := by rw [← mul_pow]; norm_num
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (1.28 : ℝ) ^ gA ≤ Real.exp (1 / 4) ^ gA := pow_le_pow_left₀ (by norm_num) cab_exp_quarter gA
      _ = Real.exp (gA / 4) := by rw [← Real.exp_nat_mul]; ring_nf
  have hexp : Real.exp (gA / 4) * Real.exp (c * Real.log (q * c)) * Real.exp (5 * Real.pi * c) *
      Real.exp (-((Real.pi - 2) * t0)) ≤ 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
    have hcl : (c : ℝ) * Real.log (q * c) = c * Real.log (q * c) := rfl
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have hg0 : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
    nlinarith [mul_le_mul_of_nonneg_left hC5 (by linarith : (0 : ℝ) ≤ (Real.pi - 2) / 2),
      mul_le_mul_of_nonneg_left hC6 (by linarith : (0 : ℝ) ≤ (Real.pi - 2) / 2)]
  calc (5.12 : ℝ) ^ gA * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0))
      ≤ (4 ^ gA * Real.exp (gA / 4)) * Real.exp (c * Real.log (q * c)) * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0)) := by gcongr
    _ = 4 ^ gA * (Real.exp (gA / 4) * Real.exp (c * Real.log (q * c)) * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0))) := by ring
    _ ≤ 4 ^ gA * 1 := by gcongr
    _ = 4 ^ gA := mul_one _

/- English proof (translation)
Establish `hq0 : 0 < q` using `by linarith`. Establish `hqc : 0 < q * (c + 1)` using `by positivity`. Establish `hf1 : (1 : ℝ) ≤ c.factorial` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)`. Use `set Y := (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) * (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) with hY`. Establish `hY0 : 0 ≤ Y` using `by positivity`.

Use `set Bsq := 12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c with hBsq`. Establish `hB0 : 0 ≤ Bsq` using `by positivity`. Use `set RHS := 7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * c.factorial with hRHS`. Establish `hR0 : 0 ≤ RHS` using `by positivity`. Establish `hr : ((q * (c + 1)) ^ ((c : ℝ) / 2)) ^ 2 = (q * (c + 1)) ^ c`.

Rewrite using `[← Real.rpow_natCast _ 2, ← Real.rpow_mul hqc.le, ← Real.rpow_natCast]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : Real.exp (-(Real.pi * t0)) = Real.exp (-((Real.pi - 2) * t0)) * Real.exp (-2 * t0)`.

Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (2 * (c + 1) / Real.pi) ^ c = (2 / (q * Real.pi)) ^ c * (q * (c + 1)) ^ c`. Rewrite using `[← mul_pow]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hY2 : Y ^ 2 = (q * (c + 1)) ^ c * Real.exp (5 * Real.pi * c) * (4 * 81 ^ g' * Real.exp (-(Real.pi * t0)))`. Rewrite using `[hY, mul_pow, mul_pow, hr, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, show (81 : ℝ) ^ g' = (9 ^ g') ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]`. Put the polynomial expressions in normal form.

Establish `hBY : Bsq * Y ^ 2 = 48 * c.factorial * 81 ^ g' * Real.exp (-2 * t0) * ((5.12 : ℝ) ^ G * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) * Real.exp (-((Real.pi - 2) * t0)))`. Rewrite using `[hY2, e1, e2, hBsq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hK` using `cab_key c gA q t0 hq dst (Nat.cast_nonneg dst) hC5 hC6`. Establish `h81 : (81 : ℝ) ^ g' ≤ 18.49 ^ dst`.

Combine the equalities or inequalities in the displayed calculation. Establish `hG' : (5.12 : ℝ) ^ G ≤ 5.12 ^ gA` using `pow_le_pow_right₀ (by norm_num) hG`. Establish `hsq : Bsq * Y ^ 2 ≤ RHS ^ 2`. Rewrite using `[hBY]`. Establish `hRHS2 : RHS ^ 2 = 49 * c.factorial * c.factorial * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA`.

Rewrite using `[hRHS, show (18.49 : ℝ) ^ dst = ((4.3 : ℝ) ^ dst) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num, show Real.exp (-2 * t0) = Real.exp (-t0) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf, show (4 : ℝ) ^ gA = ((2 : ℝ) ^ gA) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hRHS2]`. Establish `hX : (5.12 : ℝ) ^ G * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) * Real.exp (-((Real.pi - 2) * t0)) ≤ 4 ^ gA`. Use `le_trans ?_ hK` and prove the remaining obligations.

Use `gcongr`. Establish `hE : 0 ≤ Real.exp (-2 * t0)` using `(Real.exp_pos _).le`. Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ (18.49 : ℝ) ^ dst * Real.exp (-2 * t0) * 4 ^ gA` using `by positivity`. Establish `h2 : 48 * (c.factorial : ℝ) ≤ 49 * c.factorial * c.factorial` using `by nlinarith`.

Combine the equalities or inequalities in the displayed calculation. Establish `hL : Real.sqrt Bsq * (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) * (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) = Real.sqrt Bsq * Y`. Rewrite using `[hY]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul hB0, Real.sqrt_sq hY0]`. Use `_ ≤ Real.sqrt (RHS ^ 2) := Real.sqrt_le_sqrt hsq`. Use `_ = RHS := Real.sqrt_sq hR0`.
-/
theorem cab_numeric (c G gA g' dst : ℕ) (q t0 : ℝ) (hq : 2 ≤ q) (hG : G ≤ gA) (hg' : 2 * g' ≤ dst)
    (hC5 : 4 * c * (7 + Real.log (q * c)) + dst + 1 ≤ t0) (hC6 : gA * Real.log 2 ≤ t0) :
    Real.sqrt (12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c) *
        (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
        (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) ≤
      7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * c.factorial := by
  have hq0 : 0 < q := by linarith
  have hqc : 0 < q * (c + 1) := by positivity
  have hf1 : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)
  set Y := (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
    (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) with hY
  have hY0 : 0 ≤ Y := by positivity
  set Bsq := 12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c with hBsq
  have hB0 : 0 ≤ Bsq := by positivity
  set RHS := 7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * c.factorial with hRHS
  have hR0 : 0 ≤ RHS := by positivity
  have hr : ((q * (c + 1)) ^ ((c : ℝ) / 2)) ^ 2 = (q * (c + 1)) ^ c := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hqc.le, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have e1 : Real.exp (-(Real.pi * t0)) = Real.exp (-((Real.pi - 2) * t0)) * Real.exp (-2 * t0) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : (2 * (c + 1) / Real.pi) ^ c = (2 / (q * Real.pi)) ^ c * (q * (c + 1)) ^ c := by
    rw [← mul_pow]; congr 1; field_simp
  have hY2 : Y ^ 2 = (q * (c + 1)) ^ c * Real.exp (5 * Real.pi * c) * (4 * 81 ^ g' * Real.exp (-(Real.pi * t0))) := by
    rw [hY, mul_pow, mul_pow, hr, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      show (81 : ℝ) ^ g' = (9 ^ g') ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    ring_nf
  have hBY : Bsq * Y ^ 2 = 48 * c.factorial * 81 ^ g' * Real.exp (-2 * t0) *
      ((5.12 : ℝ) ^ G * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0))) := by
    rw [hY2, e1, e2, hBsq]; ring
  have hK := cab_key c gA q t0 hq dst (Nat.cast_nonneg dst) hC5 hC6
  have h81 : (81 : ℝ) ^ g' ≤ 18.49 ^ dst := by
    calc (81 : ℝ) ^ g' = 9 ^ (2 * g') := by rw [pow_mul]; norm_num
      _ ≤ 9 ^ dst := pow_le_pow_right₀ (by norm_num) hg'
      _ ≤ 18.49 ^ dst := pow_le_pow_left₀ (by norm_num) (by norm_num) dst
  have hG' : (5.12 : ℝ) ^ G ≤ 5.12 ^ gA := pow_le_pow_right₀ (by norm_num) hG
  have hsq : Bsq * Y ^ 2 ≤ RHS ^ 2 := by
    rw [hBY]
    have hRHS2 : RHS ^ 2 = 49 * c.factorial * c.factorial * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA := by
      rw [hRHS, show (18.49 : ℝ) ^ dst = ((4.3 : ℝ) ^ dst) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
        show Real.exp (-2 * t0) = Real.exp (-t0) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
        show (4 : ℝ) ^ gA = ((2 : ℝ) ^ gA) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      ring
    rw [hRHS2]
    have hX : (5.12 : ℝ) ^ G * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0)) ≤ 4 ^ gA := by
      refine le_trans ?_ hK
      gcongr
    have hE : 0 ≤ Real.exp (-2 * t0) := (Real.exp_pos _).le
    calc 48 * (c.factorial : ℝ) * 81 ^ g' * Real.exp (-2 * t0) *
          ((5.12 : ℝ) ^ G * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
            Real.exp (-((Real.pi - 2) * t0)))
        ≤ 48 * (c.factorial : ℝ) * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA := by gcongr
      _ ≤ 49 * c.factorial * c.factorial * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA := by
        have : 0 ≤ (18.49 : ℝ) ^ dst * Real.exp (-2 * t0) * 4 ^ gA := by positivity
        have h2 : 48 * (c.factorial : ℝ) ≤ 49 * c.factorial * c.factorial := by nlinarith
        calc 48 * (c.factorial : ℝ) * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA
            = (48 * (c.factorial : ℝ)) * ((18.49 : ℝ) ^ dst * Real.exp (-2 * t0) * 4 ^ gA) := by ring
          _ ≤ (49 * c.factorial * c.factorial) * ((18.49 : ℝ) ^ dst * Real.exp (-2 * t0) * 4 ^ gA) :=
            mul_le_mul_of_nonneg_right h2 this
          _ = _ := by ring
  have hL : Real.sqrt Bsq * (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
      (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) = Real.sqrt Bsq * Y := by
    rw [hY]; ring
  rw [hL]
  calc Real.sqrt Bsq * Y = Real.sqrt (Bsq * Y ^ 2) := by
        rw [Real.sqrt_mul hB0, Real.sqrt_sq hY0]
    _ ≤ Real.sqrt (RHS ^ 2) := Real.sqrt_le_sqrt hsq
    _ = RHS := Real.sqrt_sq hR0

end

end

section

noncomputable section

/- English proof (translation)
Use `set sk := Real.sqrt k with hsk`. Establish `hsk0 : 0 < sk` using `Real.sqrt_pos.mpr hk`. Establish `hsk2 : sk ^ 2 = k` using `Real.sq_sqrt hk.le`. Use `set R0 := 4 * sk * δ with hR0`. Establish `hR00 : 0 < R0` using `by positivity`.

Set `h : κ → ℝ` to `fun a => 4 * sk * ‖U a‖`. Establish `hsq : ∀ t : ℝ, Real.exp (-(4 * sk * t) ^ 2 / 16) = Real.exp (-(k * t ^ 2))`. Introduce `t`. Use `congr 1`. Rewrite using `[mul_pow, mul_pow, hsk2]`.

Expand and normalize the polynomial expressions, which then agree. Set `e` to `stdOrthonormalBasis ℝ W`. Establish `hcount : ∀ R : ℝ, R0 ≤ R → ∀ S : Finset κ, (∀ i ∈ S, h i ≤ R) → (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g')`. Introduce `R hR S hS`. Use `set R' := R / (4 * sk) with hR'`.

Establish `h4 : 0 < 4 * sk` using `by positivity`. Establish `hδR : δ ≤ R'`. Rewrite using `[hR', le_div_iff₀ h4]`. Rewrite `hR` using `[hR0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `P : Finset (EuclideanSpace ℝ (Fin (Module.finrank ℝ W)))` to `S.image (fun a => e.repr (U a))`. Establish `hinj : Set.InjOn (fun a => e.repr (U a)) S`. Introduce `a _ b _ hab`. Assume the negation of the conclusion as `hne`. Establish `h1` using `hsep a b hne`.

Simplify using `only at hab`. Establish `h2 : U a = U b` using `e.repr.injective hab`. Rewrite `h1` using `[h2, sub_self, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard : P.card = S.card` using `Finset.card_image_of_injOn hinj`.

Establish `hPn : ∀ x ∈ P, ‖x‖ ≤ R'`. Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `Finset.mem_image.mp hx`. Rewrite using `[LinearIsometryEquiv.norm_map, hR', le_div_iff₀ h4]`. Use `hS a ha` as an intermediate fact.

Simplify using `only [h] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hPs : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y`. Introduce `x hx y hy hxy`. Take `⟨a, ha, rfl⟩` from `Finset.mem_image.mp hx`.

Take `⟨b, hb, rfl⟩` from `Finset.mem_image.mp hy`. Establish `hab : a ≠ b` using `fun hab => hxy (by rw [hab])`. Rewrite using `[dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map]`. Conclude with `hsep a b hab`. Use `hP _ P δ R' hδ hδR hPn hPs` as an intermediate fact.

Rewrite `this` using `[hcard, hN]`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[hR', hR0]`. Clear the denominators using the available nonvanishing facts.

Establish `hlowh : ∀ a, R0 ≤ h a` using `fun a => by`. Simplify using `only [h, hR0]; exact mul_le_mul_of_nonneg_left (hlow a) (by positivity)`. Establish `hbig' : 16 * (2 * (g' : ℝ) + 1) ≤ R0 ^ 2`. Rewrite using `[hR0, mul_pow, mul_pow, hsk2]`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨hs, hle⟩` from `hA κ h g' R0 hR00 hbig' hlowh hcount`. Establish `hfun : (fun a => Real.exp (-(h a) ^ 2 / 16)) = fun a => Real.exp (-(k * ‖U a‖ ^ 2))`. Use function extensionality and compare the values at `a`. Conclude with `hsq _`. Rewrite `hs`, `hle` using `[hfun]`.

Use `⟨hs, hle.trans (le_of_eq ?_)⟩` and prove the remaining obligations. Rewrite using `[hR0, hsq]`.
-/
theorem cab_tail (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) {κ : Type}
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (g' : ℕ) (hN : Module.finrank ℝ W = 2 * g') (U : κ → W) (δ k : ℝ) (hδ : 0 < δ) (hk : 0 < k)
    (hsep : ∀ a b, a ≠ b → δ ≤ ‖U a - U b‖) (hlow : ∀ a, δ ≤ ‖U a‖)
    (hbig : 2 * (g' : ℝ) + 1 ≤ k * δ ^ 2) :
    Summable (fun a => Real.exp (-(k * ‖U a‖ ^ 2))) ∧
      ∑' a, Real.exp (-(k * ‖U a‖ ^ 2)) ≤ 2 * 9 ^ g' * Real.exp (-(k * δ ^ 2)) := by
  classical
  set sk := Real.sqrt k with hsk
  have hsk0 : 0 < sk := Real.sqrt_pos.mpr hk
  have hsk2 : sk ^ 2 = k := Real.sq_sqrt hk.le
  set R0 := 4 * sk * δ with hR0
  have hR00 : 0 < R0 := by positivity
  let h : κ → ℝ := fun a => 4 * sk * ‖U a‖
  have hsq : ∀ t : ℝ, Real.exp (-(4 * sk * t) ^ 2 / 16) = Real.exp (-(k * t ^ 2)) := by
    intro t; congr 1; rw [mul_pow, mul_pow, hsk2]; ring
  let e := stdOrthonormalBasis ℝ W
  have hcount : ∀ R : ℝ, R0 ≤ R → ∀ S : Finset κ, (∀ i ∈ S, h i ≤ R) →
      (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g') := by
    intro R hR S hS
    set R' := R / (4 * sk) with hR'
    have h4 : 0 < 4 * sk := by positivity
    have hδR : δ ≤ R' := by
      rw [hR', le_div_iff₀ h4]; rw [hR0] at hR; linarith
    let P : Finset (EuclideanSpace ℝ (Fin (Module.finrank ℝ W))) := S.image (fun a => e.repr (U a))
    have hinj : Set.InjOn (fun a => e.repr (U a)) S := by
      intro a _ b _ hab
      by_contra hne
      have h1 := hsep a b hne
      simp only at hab
      have h2 : U a = U b := e.repr.injective hab
      rw [h2, sub_self, norm_zero] at h1
      linarith
    have hcard : P.card = S.card := Finset.card_image_of_injOn hinj
    have hPn : ∀ x ∈ P, ‖x‖ ≤ R' := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      rw [LinearIsometryEquiv.norm_map, hR', le_div_iff₀ h4]
      have := hS a ha
      simp only [h] at this; linarith
    have hPs : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y := by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      have hab : a ≠ b := fun hab => hxy (by rw [hab])
      rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map]
      exact hsep a b hab
    have := hP _ P δ R' hδ hδR hPn hPs
    rw [hcard, hN] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [hR', hR0]; field_simp
  have hlowh : ∀ a, R0 ≤ h a := fun a => by
    simp only [h, hR0]; exact mul_le_mul_of_nonneg_left (hlow a) (by positivity)
  have hbig' : 16 * (2 * (g' : ℝ) + 1) ≤ R0 ^ 2 := by
    rw [hR0, mul_pow, mul_pow, hsk2]; nlinarith
  obtain ⟨hs, hle⟩ := hA κ h g' R0 hR00 hbig' hlowh hcount
  have hfun : (fun a => Real.exp (-(h a) ^ 2 / 16)) = fun a => Real.exp (-(k * ‖U a‖ ^ 2)) := by
    funext a; exact hsq _
  rw [hfun] at hs hle
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  rw [hR0, hsq]

end

end

end ReciprocityTheory.ChartRestriction.G.I2
