import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructC
import Formalism.PeriodIntegrals.ZerosWindowIn

noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

/- English proof (translation)
Conclude with `Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)` after adjusting the coercions.
-/
lemma one_le_level (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

def LL (N : ℕ) (t : ℝ) : ℝ := Real.log (N * (|t| + 2))

/- English proof (translation)
Establish `h1` using `one_le_level N`. Establish `h2 : (2 : ℝ) ≤ |t| + 2` using `by linarith [abs_nonneg t]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma two_le_arg (N : ℕ) [NeZero N] (t : ℝ) : (2 : ℝ) ≤ N * (|t| + 2) := by
  have h1 := one_le_level N
  have h2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  calc (2 : ℝ) = 1 * 2 := by ring
    _ ≤ N * (|t| + 2) := mul_le_mul h1 h2 (by norm_num) (by linarith)

/- English proof (translation)
The claim follows from `Real.log_le_log (by norm_num) (two_le_arg N t)`.
-/
lemma log_two_le_LL (N : ℕ) [NeZero N] (t : ℝ) : Real.log 2 ≤ LL N t := Real.log_le_log (by norm_num) (two_le_arg N t)

/- English proof (translation)
Establish `h1` using `log_two_le_LL N t`. Establish `h2` using `Real.log_two_gt_d9`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_le_two_LL (N : ℕ) [NeZero N] (t : ℝ) : 1 ≤ 2 * LL N t := by
  have h1 := log_two_le_LL N t
  have h2 := Real.log_two_gt_d9
  linarith

/- English proof (translation)
Unfold `Lent del1`. Use `split_ifs with h`. Substitute `h` using the available equality. Establish `e : DirichletCharacter.LFunctionTrivChar₁ N z = (z - 1) * DirichletCharacter.LFunctionTrivChar N z`. Simplify using `[DirichletCharacter.LFunctionTrivChar₁, hz]`.

Rewrite using `[e]`. Use `show (z - 1) * LFunction 1 z = (1 + 1 * (z - 2)) * LFunction 1 z`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
lemma Lent_eq (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : z ≠ 1) :
    Lent χ z = (1 + del1 χ * (z - 2)) * LFunction χ z := by
  unfold Lent del1
  split_ifs with h
  · subst h
    have e : DirichletCharacter.LFunctionTrivChar₁ N z =
        (z - 1) * DirichletCharacter.LFunctionTrivChar N z := by
      simp [DirichletCharacter.LFunctionTrivChar₁, hz]
    rw [e]
    show (z - 1) * LFunction 1 z = (1 + 1 * (z - 2)) * LFunction 1 z
    ring
  · simp

/- English proof (translation)
Rewrite using `[Lent_eq χ hz]`. Use `(hG N χ hχ z h1 h2).trans ?_` and prove the remaining obligations. Establish `hN` using `one_le_level N`. Establish `hb : (N : ℝ) * (|z.im| + 2) ≤ 4 * (N * (|t| + 2))`. Use `mul_le_mul_of_nonneg_left (show |z.im| + 2 ≤ 4 * (|t| + 2) by linarith [abs_nonneg t]) (show (0 : ℝ) ≤ N by linarith)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hA.le) hC.le`.
-/
lemma Lent_bound_ne {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {z : ℂ} (h1 : -4 ≤ z.re)
    (h2 : z.re ≤ 8) (h3 : |z.im| ≤ |t| + 6) (hz : z ≠ 1) :
    ‖Lent χ z‖ ≤ C * (4 * (N * (|t| + 2))) ^ A := by
  rw [Lent_eq χ hz]
  refine (hG N χ hχ z h1 h2).trans ?_
  have hN := one_le_level N
  have hb : (N : ℝ) * (|z.im| + 2) ≤ 4 * (N * (|t| + 2)) := by
    have := mul_le_mul_of_nonneg_left (show |z.im| + 2 ≤ 4 * (|t| + 2) by linarith [abs_nonneg t])
      (show (0 : ℝ) ≤ N by linarith)
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hA.le) hC.le

/- English proof (translation)
Distinguish the cases in `hz : z = 1`. Substitute `hz` using the available equality. Establish `hcont : Continuous (Lent χ)`. Unfold `Lent`. Use `split_ifs with h`.

Conclude with `(DirichletCharacter.differentiable_LFunctionTrivChar₁ N).continuous`. Conclude with `(DirichletCharacter.differentiable_LFunction h).continuous`. Establish `hc : Continuous (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖)` using `(hcont.comp (continuous_const.add Complex.continuous_ofReal)).norm`. Establish `h0 : ‖Lent χ 1‖ = ‖Lent χ (1 + ((0 : ℝ) : ℂ))‖` using `by simp`. Establish `hT : Filter.Tendsto (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds ‖Lent χ 1‖)`.

Rewrite using `[h0]`. Conclude with `(hc.tendsto 0).mono_left nhdsWithin_le_nhds`. Use `le_of_tendsto hT ?_` and prove the remaining obligations. Establish `hmem : Set.Ioo (-1 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) {0}ᶜ` using `nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))`. Use `filter_upwards [hmem, self_mem_nhdsWithin] with x hx hx0`.

Establish `hx1 : (1 + (x : ℂ)) ≠ 1`. Introduce `h`. Apply `hx0` to reduce the goal to its premises. Establish `h'` using `congrArg Complex.re h`. Simplify using `only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at h'`.

Use `show x = 0`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Lent_bound_ne hA hC hG hχ ?_ ?_ ?_ hx1` and prove the remaining obligations. Simplify using `only [Complex.add_re, Complex.one_re, Complex.ofReal_re]`. Combine the linear relations using `[hx.1]`.

Simplify using `only [Complex.add_re, Complex.one_re, Complex.ofReal_re]`. Combine the linear relations using `[hx.2]`. Simplify using `only [Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero, abs_zero]`. Check the signs of the components of the expression. Conclude with `Lent_bound_ne hA hC hG hχ h1 h2 h3 hz`.
-/
lemma Lent_bound {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {z : ℂ} (h1 : -4 ≤ z.re)
    (h2 : z.re ≤ 8) (h3 : |z.im| ≤ |t| + 6) :
    ‖Lent χ z‖ ≤ C * (4 * (N * (|t| + 2))) ^ A := by
  by_cases hz : z = 1
  · subst hz
    have hcont : Continuous (Lent χ) := by
      unfold Lent
      split_ifs with h
      · exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).continuous
      · exact (DirichletCharacter.differentiable_LFunction h).continuous
    have hc : Continuous (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) :=
      (hcont.comp (continuous_const.add Complex.continuous_ofReal)).norm
    have h0 : ‖Lent χ 1‖ = ‖Lent χ (1 + ((0 : ℝ) : ℂ))‖ := by simp
    have hT : Filter.Tendsto (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhds ‖Lent χ 1‖) := by
      rw [h0]
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hT ?_
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) {0}ᶜ :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [hmem, self_mem_nhdsWithin] with x hx hx0
    have hx1 : (1 + (x : ℂ)) ≠ 1 := by
      intro h
      apply hx0
      have h' := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at h'
      show x = 0
      linarith
    refine Lent_bound_ne hA hC hG hχ ?_ ?_ ?_ hx1
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith [hx.1]
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith [hx.2]
    · simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero, abs_zero]
      positivity
  · exact Lent_bound_ne hA hC hG hχ h1 h2 h3 hz

def ctr (t : ℝ) : ℂ := 2 + t * I

/- English proof (translation)
Simplify using `[ctr]`.
-/
@[simp] lemma ctr_re (t : ℝ) : (ctr t).re = 2 := by
  simp [ctr]
/- English proof (translation)
Simplify using `[ctr]`.
-/
@[simp] lemma ctr_im (t : ℝ) : (ctr t).im = t := by
  simp [ctr]

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg Complex.re h`. Rewrite `h'` using `[ctr_re]`. Evaluate the numerical expressions using `at h'`.
-/
lemma ctr_ne_one (t : ℝ) : ctr t ≠ 1 := by
  intro h
  have h' := congrArg Complex.re h
  rw [ctr_re] at h'
  norm_num at h'

/- English proof (translation)
Establish `hL` using `hI N χ (ctr t) (by rw [ctr_re]; norm_num)`. Establish `h21 : (2 : ℝ) / (2 - 1) = 2` using `by norm_num`. Rewrite `hL` using `[ctr_re, h21]`. Establish `hne` using `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (s := ctr t) (Or.inr (ctr_ne_one t)) (by rw [ctr_re]; norm_num)`. Establish `hpos : 0 < ‖LFunction χ (ctr t)‖` using `norm_pos_iff.mpr hne`.

Establish `hL2 : 1 / 2 ≤ ‖LFunction χ (ctr t)‖`. Establish `h1` using `mul_le_mul_of_nonneg_left hL hpos.le`. Rewrite `h1` using `[mul_inv_cancel₀ hpos.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Lent_eq χ (ctr_ne_one t), norm_mul]`.

Establish `hf : 1 ≤ ‖1 + del1 χ * (ctr t - 2)‖`. Establish `hre : (1 + del1 χ * (ctr t - 2)).re = 1`. Unfold `del1 ctr`. Apply the tactic sequence `split_ifs <;> norm_num`. Use `Complex.abs_re_le_norm (1 + del1 χ * (ctr t - 2))` as an intermediate fact.

Rewrite `this` using `[hre, abs_one]`. Conclude with `this`. Use `mul_le_mul hf hL2 (by norm_num) (by positivity)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma half_le_norm_Lent_ctr (hI : PI.LInvRight) (χ : DirichletCharacter ℂ N) (t : ℝ) :
    1 / 2 ≤ ‖Lent χ (ctr t)‖ := by
  have hL := hI N χ (ctr t) (by rw [ctr_re]; norm_num)
  have h21 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  rw [ctr_re, h21] at hL
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (s := ctr t)
    (Or.inr (ctr_ne_one t)) (by rw [ctr_re]; norm_num)
  have hpos : 0 < ‖LFunction χ (ctr t)‖ := norm_pos_iff.mpr hne
  have hL2 : 1 / 2 ≤ ‖LFunction χ (ctr t)‖ := by
    have h1 := mul_le_mul_of_nonneg_left hL hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at h1
    linarith
  rw [Lent_eq χ (ctr_ne_one t), norm_mul]
  have hf : 1 ≤ ‖1 + del1 χ * (ctr t - 2)‖ := by
    have hre : (1 + del1 χ * (ctr t - 2)).re = 1 := by
      unfold del1 ctr
      split_ifs <;> norm_num
    have := Complex.abs_re_le_norm (1 + del1 χ * (ctr t - 2))
    rw [hre, abs_one] at this
    exact this
  have := mul_le_mul hf hL2 (by norm_num) (by positivity)
  linarith

def Mfun (A C : ℝ) (N : ℕ) (t : ℝ) : ℝ := |Real.log (2 * C)| + A * Real.log (4 * (N * (|t| + 2)))

/- English proof (translation)
Unfold `Mfun`. Establish `h` using `two_le_arg N t`. Establish `h3 : 0 ≤ Real.log (4 * (N * (|t| + 2)))` using `Real.log_nonneg (by linarith)`. Establish `h4` using `abs_nonneg (Real.log (2 * C))`. Establish `h5` using `mul_nonneg hA.le h3`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma Mfun_nonneg {A C : ℝ} (hA : 0 < A) (N : ℕ) [NeZero N] (t : ℝ) : 0 ≤ Mfun A C N t := by
  unfold Mfun
  have h := two_le_arg N t
  have h3 : 0 ≤ Real.log (4 * (N * (|t| + 2))) := Real.log_nonneg (by linarith)
  have h4 := abs_nonneg (Real.log (2 * C))
  have h5 := mul_nonneg hA.le h3
  linarith

/- English proof (translation)
Unfold `Mfun`. Establish `hX : (0 : ℝ) < N * (|t| + 2)` using `by linarith [two_le_arg N t]`. Establish `h4 : Real.log (4 * (N * (|t| + 2))) = Real.log 4 + LL N t`. Rewrite using `[Real.log_mul (by norm_num) hX.ne']`. Both sides reduce to the same expression.

Establish `hl4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Evaluate the numerical expressions. Establish `h1` using `one_le_two_LL N t`. Establish `h2` using `log_two_le_LL N t`.

Establish `ha` using `abs_nonneg (Real.log (2 * C))`. Rewrite using `[h4, hl4]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hA.le]`.
-/
lemma Mfun_le {A C : ℝ} (hA : 0 < A) (N : ℕ) [NeZero N] (t : ℝ) :
    Mfun A C N t ≤ (2 * |Real.log (2 * C)| + 3 * A) * LL N t := by
  unfold Mfun
  have hX : (0 : ℝ) < N * (|t| + 2) := by linarith [two_le_arg N t]
  have h4 : Real.log (4 * (N * (|t| + 2))) = Real.log 4 + LL N t := by
    rw [Real.log_mul (by norm_num) hX.ne']
    rfl
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h1 := one_le_two_LL N t
  have h2 := log_two_le_LL N t
  have ha := abs_nonneg (Real.log (2 * C))
  rw [h4, hl4]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hA.le]

/- English proof (translation)
Unfold `Mfun`. Establish `hY : (0 : ℝ) < 4 * (N * (|t| + 2))` using `by linarith [two_le_arg N t]`. Rewrite using `[Real.exp_add, Real.rpow_def_of_pos hY, mul_comm (Real.log (4 * (N * (|t| + 2)))) A]`. Establish `h2C : 2 * C ≤ Real.exp |Real.log (2 * C)|`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `mul_le_mul_of_nonneg_right h2C (Real.exp_pos _).le`.
-/
lemma le_exp_Mfun {A C : ℝ} (hC : 0 < C) (N : ℕ) [NeZero N] (t : ℝ) :
    2 * C * (4 * (N * (|t| + 2))) ^ A ≤ Real.exp (Mfun A C N t) := by
  unfold Mfun
  have hY : (0 : ℝ) < 4 * (N * (|t| + 2)) := by linarith [two_le_arg N t]
  rw [Real.exp_add, Real.rpow_def_of_pos hY, mul_comm (Real.log (4 * (N * (|t| + 2)))) A]
  have h2C : 2 * C ≤ Real.exp |Real.log (2 * C)| := by
    calc 2 * C = Real.exp (Real.log (2 * C)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_abs_self _)
  exact mul_le_mul_of_nonneg_right h2C (Real.exp_pos _).le

/- English proof (translation)
Introduce `z hz`. Establish `hz' : ‖z - ctr t‖ ≤ 6` using `by rwa [Metric.mem_closedBall, dist_eq_norm] at hz`. Establish `hre` using `(Complex.abs_re_le_norm (z - ctr t)).trans hz'`. Establish `him` using `(Complex.abs_im_le_norm (z - ctr t)).trans hz'`. Rewrite `hre` using `[Complex.sub_re, ctr_re]`.

Rewrite `him` using `[Complex.sub_im, ctr_im]`. Establish `h1 : -4 ≤ z.re` using `by linarith [neg_abs_le (z.re - 2)]`. Establish `h2 : z.re ≤ 8` using `by linarith [le_abs_self (z.re - 2)]`. Establish `h3 : |z.im| ≤ |t| + 6`. Use `abs_sub_abs_le_abs_sub z.im t` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb` using `Lent_bound hA hC hG hχ h1 h2 h3`. Establish `he` using `le_exp_Mfun (A := A) hC N t`. Establish `hh` using `half_le_norm_Lent_ctr hI χ t`. Establish `hE` using `Real.exp_pos (Mfun A C N t)`.

Establish `hP : 0 ≤ C * (4 * (N * (|t| + 2))) ^ A` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hh hE.le]`.
-/
theorem Lent_disc_bound {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C) (hI : PI.LInvRight)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (t : ℝ) :
    ∀ z ∈ closedBall (ctr t) 6, ‖Lent χ z‖ ≤ Real.exp (Mfun A C N t) * ‖Lent χ (ctr t)‖ := by
  intro z hz
  have hz' : ‖z - ctr t‖ ≤ 6 := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - ctr t)).trans hz'
  have him := (Complex.abs_im_le_norm (z - ctr t)).trans hz'
  rw [Complex.sub_re, ctr_re] at hre
  rw [Complex.sub_im, ctr_im] at him
  have h1 : -4 ≤ z.re := by linarith [neg_abs_le (z.re - 2)]
  have h2 : z.re ≤ 8 := by linarith [le_abs_self (z.re - 2)]
  have h3 : |z.im| ≤ |t| + 6 := by
    have := abs_sub_abs_le_abs_sub z.im t
    linarith
  have hb := Lent_bound hA hC hG hχ h1 h2 h3
  have he := le_exp_Mfun (A := A) hC N t
  have hh := half_le_norm_Lent_ctr hI χ t
  have hE := Real.exp_pos (Mfun A C N t)
  have hP : 0 ≤ C * (4 * (N * (|t| + 2))) ^ A := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hh hE.le]

end PI.EF
