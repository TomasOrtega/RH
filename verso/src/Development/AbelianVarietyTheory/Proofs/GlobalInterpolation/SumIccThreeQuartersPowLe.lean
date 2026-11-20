import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedFejerPositivityStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `J with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Rewrite using `[pow_succ]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_Icc_three_quarters_pow_le (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 3 - 3 * (3 / 4 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [pow_succ]
    linarith

/- English proof (translation)
Take `⟨i₁, hi₁, hmax⟩` from `Finset.exists_max_image (S.filter fun i => 1 ≤ b i) (fun i => ‖z i‖) ⟨i₀, Finset.mem_filter.2 ⟨hi, hb⟩⟩`. Take `⟨hi₁S, hb₁⟩` from `Finset.mem_filter.1 hi₁`. Use `set R : ℝ := ‖z i₁‖ with hR`. Establish `h1x : 0 < 1 + x` using `by linarith`. Establish `hRge : 1 / (1 + x) ≤ R` using `hz.trans (hmax i₀ (Finset.mem_filter.2 ⟨hi, hb⟩))`.

Establish `hRpos : 0 < R` using `lt_of_lt_of_le (by positivity) hRge`. Establish `hRinv : R⁻¹ ≤ 1 + x`. Rewrite using `[inv_le_comm₀ hRpos h1x, ← one_div]`. Conclude with `hRge`. Establish `hRinv0 : 0 ≤ R⁻¹` using `by positivity`.

Use `set θ : ℝ := Complex.arg (z i₁) with hθ`. Take `⟨hF1, hF2⟩` from `GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound J θ`. Use `set c : ℕ → ℝ := fun j => (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) with hc`. Use `set F : ℂ → ℝ := fun w => ∑ j ∈ Finset.Icc 1 J, c j * (w ^ j).re with hF`. Establish `hF1' : ∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ F w` using `hF1`.

Establish `hF2' : (J : ℝ) / 4 - 3 / 4 ≤ F (Complex.exp (θ * I))` using `hF2`. Use `set w : ι → ℂ := fun i => ((R⁻¹ : ℝ) : ℂ) * z i with hw`. Establish `hw₁ : w i₁ = Complex.exp (θ * I)`. Establish `h` using `Complex.norm_mul_exp_arg_mul_I (z i₁)`. Establish `hR' : (R : ℂ) ≠ 0` using `by exact_mod_cast hRpos.ne'`.

Use `show ((R⁻¹ : ℝ) : ℂ) * z i₁ = _`. Rewrite using `[← h]`. Use `push_cast`. Rewrite using `[← hR, ← hθ, ← mul_assoc, inv_mul_cancel₀ hR', one_mul]`. Establish `hwn : ∀ i ∈ S, 1 ≤ b i → ‖w i‖ ≤ 1`.

Introduce `i hiS hbi`. Use `hmax i (Finset.mem_filter.2 ⟨hiS, hbi⟩)` as an intermediate fact. Use `show ‖((R⁻¹ : ℝ) : ℂ) * z i‖ ≤ 1`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hRinv0, inv_mul_le_iff₀ hRpos, mul_one]`. Conclude with `this`.

Establish `hlow : (J : ℝ) / 4 - L ≤ ∑ i ∈ S, (b i : ℝ) * F (w i)`. Establish `hnn : ∀ i ∈ S, 0 ≤ (b i : ℝ) * (F (w i) + 1)`. Introduce `i hiS`. Break down `Nat.eq_zero_or_pos (b i) with h0 | h0` into its components or cases. Simplify using `[h0]`.

Use `hF1' _ (hwn i hiS h0)` as an intermediate fact. Conclude with `mul_nonneg (Nat.cast_nonneg _) (by linarith)`. Establish `h1` using `Finset.single_le_sum hnn hi₁S`. Establish `hb1 : (1 : ℝ) ≤ b i₁` using `by exact_mod_cast hb₁`. Establish `h2` using `hF1' _ (hwn i₁ hi₁S hb₁)`.

Establish `h3 : F (w i₁) + 1 ≤ (b i₁ : ℝ) * (F (w i₁) + 1)` using `by nlinarith`. Establish `h4 : ∑ i ∈ S, (b i : ℝ) * (F (w i) + 1) = ∑ i ∈ S, (b i : ℝ) * F (w i) + ∑ i ∈ S, (b i : ℝ)`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite `hF2'` using `[← hw₁]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hex : ∑ i ∈ S, (b i : ℝ) * F (w i) = ∑ j ∈ Finset.Icc 1 J, c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)`. Simplify using `only [hF, Finset.mul_sum, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `e1 : (w i ^ j).re = R⁻¹ ^ j * (z i ^ j).re` using `by show ((((R⁻¹ : ℝ) : ℂ) * z i) ^ j).re = _`. Rewrite using `[mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Establish `e2 : ((b i : ℂ) * z i ^ j).re = (b i : ℝ) * (z i ^ j).re`. Rewrite using `[← Complex.ofReal_natCast, Complex.re_ofReal_mul]`. Rewrite using `[e1, e2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hup : ∀ j ∈ Finset.Icc 1 J, c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re) ≤ 4 * J * δ * (1 + x) ^ J + 2 * L * (3 / 4 : ℝ) ^ j`. Introduce `j hj`. Take `⟨hj1, hjJ⟩` from `Finset.mem_Icc.1 hj`. Establish `hjJ' : (j : ℝ) ≤ J` using `by exact_mod_cast hjJ`.

Establish `hJ1 : (0 : ℝ) < J + 1` using `by positivity`. Establish `ha0 : 0 ≤ 1 - (j : ℝ) / (J + 1)`. Rewrite using `[sub_nonneg, div_le_one hJ1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha1 : 1 - (j : ℝ) / (J + 1) ≤ 1`.

Establish `: 0 ≤ (j : ℝ) / (J + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcos1` using `Real.cos_le_one (j * θ)`. Establish `hcos2` using `Real.neg_one_le_cos (j * θ)`. Establish `hc0 : 0 ≤ c j` using `mul_nonneg ha0 (by linarith)`.

Establish `hc2 : c j ≤ 2` using `by show (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) ≤ 2`. Use the polynomial consequences of the given equalities and inequalities. Establish `hq : R⁻¹ ^ j ≤ (1 + x) ^ j` using `pow_le_pow_left₀ hRinv0 hRinv j`. Establish `hq2 : (1 + x) ^ j ≤ (1 + x) ^ J` using `pow_le_pow_right₀ (by linarith) hjJ`. Establish `hq3 : (1 + x) ^ j ≤ (3 / 2 : ℝ) ^ j` using `pow_le_pow_left₀ h1x.le (by linarith) j`.

Establish `hB0 : 0 ≤ 2 * j * δ + L / 2 ^ j` using `by positivity`. Establish `s1 : R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j)` using `(mul_le_mul_of_nonneg_left (hp j hj1) (by positivity)).trans (mul_le_mul_of_nonneg_right hq hB0)`. Establish `s2 : (1 + x) ^ j * (2 * j * δ) ≤ (1 + x) ^ J * (2 * J * δ)` using `by gcongr`. Establish `s3 : (1 + x) ^ j * (L / 2 ^ j) ≤ (3 / 2 : ℝ) ^ j * (L / 2 ^ j)` using `by gcongr`. Establish `s4 : (3 / 2 : ℝ) ^ j * (L / 2 ^ j) = L * (3 / 4 : ℝ) ^ j`.

Establish `: (3 / 4 : ℝ) ^ j = (3 / 2 : ℝ) ^ j / 2 ^ j` using `by rw [← div_pow]; norm_num`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `s5 : 0 ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsum` using `Finset.sum_le_sum hup`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]`. Establish `hg` using `sum_Icc_three_quarters_pow_le J`. Establish `hg0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ J` using `by positivity`. Establish `hg' : 2 * L * ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 2 * L * 3` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`.

Establish `: (J : ℝ) * (4 * J * δ * (1 + x) ^ J) = 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem powerSum_weighted_ineq {ι : Type} (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι)
    (L δ x : ℝ) (hi : i₀ ∈ S) (hb : 1 ≤ b i₀) (hL : 1 ≤ L) (hδ : 0 < δ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) (hz : 1 / (1 + x) ≤ ‖z i₀‖) (hS : (∑ i ∈ S, (b i : ℝ)) ≤ L)
    (hp : ∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) (J : ℕ) :
    (J : ℝ) / 4 - 7 * L ≤ 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by
  classical
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image (S.filter fun i => 1 ≤ b i)
    (fun i => ‖z i‖) ⟨i₀, Finset.mem_filter.2 ⟨hi, hb⟩⟩
  obtain ⟨hi₁S, hb₁⟩ := Finset.mem_filter.1 hi₁
  set R : ℝ := ‖z i₁‖ with hR
  have h1x : 0 < 1 + x := by linarith
  have hRge : 1 / (1 + x) ≤ R := hz.trans (hmax i₀ (Finset.mem_filter.2 ⟨hi, hb⟩))
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRge
  have hRinv : R⁻¹ ≤ 1 + x := by
    rw [inv_le_comm₀ hRpos h1x, ← one_div]; exact hRge
  have hRinv0 : 0 ≤ R⁻¹ := by positivity
  set θ : ℝ := Complex.arg (z i₁) with hθ
  obtain ⟨hF1, hF2⟩ := GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound J θ
  set c : ℕ → ℝ := fun j => (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) with hc
  set F : ℂ → ℝ := fun w => ∑ j ∈ Finset.Icc 1 J, c j * (w ^ j).re with hF
  have hF1' : ∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ F w := hF1
  have hF2' : (J : ℝ) / 4 - 3 / 4 ≤ F (Complex.exp (θ * I)) := hF2
  set w : ι → ℂ := fun i => ((R⁻¹ : ℝ) : ℂ) * z i with hw
  have hw₁ : w i₁ = Complex.exp (θ * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (z i₁)
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    show ((R⁻¹ : ℝ) : ℂ) * z i₁ = _
    rw [← h]
    push_cast
    rw [← hR, ← hθ, ← mul_assoc, inv_mul_cancel₀ hR', one_mul]
  have hwn : ∀ i ∈ S, 1 ≤ b i → ‖w i‖ ≤ 1 := by
    intro i hiS hbi
    have := hmax i (Finset.mem_filter.2 ⟨hiS, hbi⟩)
    show ‖((R⁻¹ : ℝ) : ℂ) * z i‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hRinv0, inv_mul_le_iff₀ hRpos, mul_one]
    exact this

  have hlow : (J : ℝ) / 4 - L ≤ ∑ i ∈ S, (b i : ℝ) * F (w i) := by
    have hnn : ∀ i ∈ S, 0 ≤ (b i : ℝ) * (F (w i) + 1) := by
      intro i hiS
      rcases Nat.eq_zero_or_pos (b i) with h0 | h0
      · simp [h0]
      · have := hF1' _ (hwn i hiS h0)
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have h1 := Finset.single_le_sum hnn hi₁S
    have hb1 : (1 : ℝ) ≤ b i₁ := by exact_mod_cast hb₁
    have h2 := hF1' _ (hwn i₁ hi₁S hb₁)
    have h3 : F (w i₁) + 1 ≤ (b i₁ : ℝ) * (F (w i₁) + 1) := by nlinarith
    have h4 : ∑ i ∈ S, (b i : ℝ) * (F (w i) + 1)
        = ∑ i ∈ S, (b i : ℝ) * F (w i) + ∑ i ∈ S, (b i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [← hw₁] at hF2'
    linarith

  have hex : ∑ i ∈ S, (b i : ℝ) * F (w i)
      = ∑ j ∈ Finset.Icc 1 J, c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re) := by
    simp only [hF, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e1 : (w i ^ j).re = R⁻¹ ^ j * (z i ^ j).re := by
      show ((((R⁻¹ : ℝ) : ℂ) * z i) ^ j).re = _
      rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have e2 : ((b i : ℂ) * z i ^ j).re = (b i : ℝ) * (z i ^ j).re := by
      rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e1, e2]; ring

  have hup : ∀ j ∈ Finset.Icc 1 J,
      c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ 4 * J * δ * (1 + x) ^ J + 2 * L * (3 / 4 : ℝ) ^ j := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.1 hj
    have hjJ' : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hJ1 : (0 : ℝ) < J + 1 := by positivity
    have ha0 : 0 ≤ 1 - (j : ℝ) / (J + 1) := by
      rw [sub_nonneg, div_le_one hJ1]; linarith
    have ha1 : 1 - (j : ℝ) / (J + 1) ≤ 1 := by
      have : 0 ≤ (j : ℝ) / (J + 1) := by positivity
      linarith
    have hcos1 := Real.cos_le_one (j * θ)
    have hcos2 := Real.neg_one_le_cos (j * θ)
    have hc0 : 0 ≤ c j := mul_nonneg ha0 (by linarith)
    have hc2 : c j ≤ 2 := by
      show (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) ≤ 2
      nlinarith
    have hq : R⁻¹ ^ j ≤ (1 + x) ^ j := pow_le_pow_left₀ hRinv0 hRinv j
    have hq2 : (1 + x) ^ j ≤ (1 + x) ^ J := pow_le_pow_right₀ (by linarith) hjJ
    have hq3 : (1 + x) ^ j ≤ (3 / 2 : ℝ) ^ j := pow_le_pow_left₀ h1x.le (by linarith) j
    have hB0 : 0 ≤ 2 * j * δ + L / 2 ^ j := by positivity
    have s1 : R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re
        ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) :=
      (mul_le_mul_of_nonneg_left (hp j hj1) (by positivity)).trans
        (mul_le_mul_of_nonneg_right hq hB0)
    have s2 : (1 + x) ^ j * (2 * j * δ) ≤ (1 + x) ^ J * (2 * J * δ) := by gcongr
    have s3 : (1 + x) ^ j * (L / 2 ^ j) ≤ (3 / 2 : ℝ) ^ j * (L / 2 ^ j) := by gcongr
    have s4 : (3 / 2 : ℝ) ^ j * (L / 2 ^ j) = L * (3 / 4 : ℝ) ^ j := by
      have : (3 / 4 : ℝ) ^ j = (3 / 2 : ℝ) ^ j / 2 ^ j := by rw [← div_pow]; norm_num
      rw [this]; ring
    have s5 : 0 ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) := by positivity
    calc c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ c j * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_left s1 hc0
      _ ≤ 2 * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_right hc2 s5
      _ ≤ _ := by rw [mul_add ((1 + x) ^ j)]; linarith
  have hsum := Finset.sum_le_sum hup
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hg := sum_Icc_three_quarters_pow_le J
  have hg0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ J := by positivity
  have hg' : 2 * L * ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 2 * L * 3 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have : (J : ℝ) * (4 * J * δ * (1 + x) ^ J) = 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by ring
  linarith

/- English proof (translation)
Use `⟨2080, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `ι S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp`. Establish `h` using `powerSum_weighted_ineq S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp ⌈64 * L⌉₊`. Use `set J : ℕ := ⌈64 * L⌉₊ with hJ`. Establish `hJ1 : 64 * L ≤ J` using `Nat.le_ceil _`.

Establish `hJ2 : (J : ℝ) ≤ 65 * L`. Use `Nat.ceil_lt_add_one (show 0 ≤ 64 * L by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hJ0 : (0 : ℝ) < J` using `by linarith`. Establish `hP : (1 + x) ^ J ≤ Real.exp (x * J)`.

Rewrite using `[mul_comm, Real.exp_nat_mul]`. Conclude with `pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) J`. Establish `hP0 : 0 < (1 + x) ^ J` using `by positivity`. Establish `h1 : (J : ℝ) * 1 ≤ J * (32 * J * δ * (1 + x) ^ J)` using `by nlinarith`. Establish `h2 : 1 ≤ 32 * J * δ * (1 + x) ^ J` using `le_of_mul_le_mul_left h1 hJ0`.

Establish `h3 : 32 * J * δ * (1 + x) ^ J ≤ 2080 * L * δ * Real.exp (x * J)`. Establish `: 32 * (J : ℝ) ≤ 2080 * L` using `by linarith`. Use `gcongr`. Establish `hD : 0 < 2080 * L * δ` using `by positivity`. Establish `h4 : 1 / (2080 * L * δ) ≤ Real.exp (x * J)`.

Rewrite using `[div_le_iff₀ hD]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : Real.log (1 / (2080 * L * δ)) ≤ x * J` using `(Real.log_le_iff_le_exp (by positivity)).2 h4`. Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `: x * J ≤ x * (2080 * L)` using `mul_le_mul_of_nonneg_left (by linarith) hx0`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem powerSum_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι) (L δ x : ℝ), i₀ ∈ S → 1 ≤ b i₀ → 1 ≤ L → 0 < δ → 0 ≤ x → x ≤ 1 / 2 → 1 / (1 + x) ≤ ‖z i₀‖ → (∑ i ∈ S, (b i : ℝ)) ≤ L → (∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) → Real.log (1 / (C * L * δ)) / (C * L) ≤ x := by
  refine ⟨2080, by norm_num, ?_⟩
  intro ι S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp
  have h := powerSum_weighted_ineq S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp ⌈64 * L⌉₊
  set J : ℕ := ⌈64 * L⌉₊ with hJ
  have hJ1 : 64 * L ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) ≤ 65 * L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 64 * L by linarith)
    linarith
  have hJ0 : (0 : ℝ) < J := by linarith
  have hP : (1 + x) ^ J ≤ Real.exp (x * J) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) J
  have hP0 : 0 < (1 + x) ^ J := by positivity
  have h1 : (J : ℝ) * 1 ≤ J * (32 * J * δ * (1 + x) ^ J) := by nlinarith
  have h2 : 1 ≤ 32 * J * δ * (1 + x) ^ J := le_of_mul_le_mul_left h1 hJ0
  have h3 : 32 * J * δ * (1 + x) ^ J ≤ 2080 * L * δ * Real.exp (x * J) := by
    have : 32 * (J : ℝ) ≤ 2080 * L := by linarith
    gcongr
  have hD : 0 < 2080 * L * δ := by positivity
  have h4 : 1 / (2080 * L * δ) ≤ Real.exp (x * J) := by
    rw [div_le_iff₀ hD]; linarith
  have h5 : Real.log (1 / (2080 * L * δ)) ≤ x * J :=
    (Real.log_le_iff_le_exp (by positivity)).2 h4
  rw [div_le_iff₀ (by positivity)]
  have : x * J ≤ x * (2080 * L) := mul_le_mul_of_nonneg_left (by linarith) hx0
  linarith

end GlobalTheory
