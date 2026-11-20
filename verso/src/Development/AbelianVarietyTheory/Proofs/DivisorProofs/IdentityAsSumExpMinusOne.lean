import Mathlib

open scoped ContDiff

namespace GlobalTheory.ExpDivision

/- English proof (translation)
Establish `hi : ∀ n, iteratedDeriv n f ∈ S`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hf`. Consider the case `succ n ih => rw [iteratedDeriv_succ]`.

Conclude with `hc _ ih`. Use `⟨contDiff_of_differentiable_iteratedDeriv fun m _ => hd _ (hi m), fun n => ?_⟩` and prove the remaining obligations. Take `⟨k, C, h⟩` from `hb _ (hi n)`. Conclude with `⟨k, C, fun x => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact h x⟩`.
-/
theorem hasTemperateGrowth_of_closed (S : Set (ℝ → ℂ))
    (hd : ∀ f ∈ S, Differentiable ℝ f) (hc : ∀ f ∈ S, deriv f ∈ S)
    (hb : ∀ f ∈ S, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    {f : ℝ → ℂ} (hf : f ∈ S) : f.HasTemperateGrowth := by
  have hi : ∀ n, iteratedDeriv n f ∈ S := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih => rw [iteratedDeriv_succ]; exact hc _ ih
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => hd _ (hi m), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hb _ (hi n)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact h x⟩

/- English proof (translation)
Use `⟨(contDiff_infty_iff_deriv.1 hf.1).2, fun n => ?_⟩` and prove the remaining obligations. Take `⟨k, C, h⟩` from `hf.2 (n + 1)`. Use `⟨k, C, fun x => ?_⟩` and prove the remaining obligations. Use `h x` as an intermediate fact. Rewrite `this`, the goal using `[norm_iteratedFDeriv_eq_norm_iteratedDeriv]`.

Rewrite `this` using `[iteratedDeriv_succ']`. Then use the resulting hypothesis.
-/
theorem hasTemperateGrowth_deriv {f : ℝ → ℂ} (hf : f.HasTemperateGrowth) :
    (deriv f).HasTemperateGrowth := by
  refine ⟨(contDiff_infty_iff_deriv.1 hf.1).2, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  refine ⟨k, C, fun x => ?_⟩
  have := h x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at this ⊢
  rwa [iteratedDeriv_succ'] at this

/- English proof (translation)
Establish `hEd : Differentiable ℝ E` using `hE.1.differentiable (by simp)`. Use `hasTemperateGrowth_of_closed {f | ∃ (m : ℕ) (u : ℝ → ℂ), u.HasTemperateGrowth ∧ f = fun x => u x / E x ^ m} ?_ ?_ ?_ ⟨1, g, hg, by simp⟩` and prove the remaining obligations. Introduce and unpack `f ⟨m, u, hu, rfl⟩`. Establish `hud : Differentiable ℝ u` using `hu.1.differentiable (by simp)`. Conclude with `hud.div (hEd.pow m) fun x => pow_ne_zero _ (h0 x)`.

Introduce and unpack `f ⟨m, u, hu, rfl⟩`. Establish `hud : Differentiable ℝ u` using `hu.1.differentiable (by simp)`. Establish `hp : (fun x => E x ^ m).HasTemperateGrowth` using `hE.pow m`. Establish `hpd : Differentiable ℝ (fun x => E x ^ m)` using `hp.1.differentiable (by simp)`. Use `⟨m * 2, fun x => deriv u x * E x ^ m - u x * deriv (fun x => E x ^ m) x, ((hasTemperateGrowth_deriv hu).mul hp).sub (hu.mul (hasTemperateGrowth_deriv hp)), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Rewrite using `[pow_mul]`. Conclude with `deriv_fun_div (hud x) (hpd x) (pow_ne_zero _ (h0 x))`. Introduce and unpack `f ⟨m, u, hu, rfl⟩`. Take `⟨k, C, h⟩` from `hu.2 0`.

Use `⟨k + N * m, C * M ^ m, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖u x‖ ≤ C * (1 + ‖x‖) ^ k` using `by simpa using h x`. Establish `h2` using `hM x`. Establish `h3 : 0 ≤ C * (1 + ‖x‖) ^ k` using `(norm_nonneg _).trans h1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_eq_mul_inv, norm_mul, ← inv_pow, norm_pow]`. Use `_ ≤ (C * (1 + ‖x‖) ^ k) * (M * (1 + ‖x‖) ^ N) ^ m := by gcongr`. Use `_ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring`.
-/
theorem hasTemperateGrowth_div {E g : ℝ → ℂ} (hE : E.HasTemperateGrowth)
    (h0 : ∀ x, E x ≠ 0) {N : ℕ} {M : ℝ} (hM : ∀ x, ‖(E x)⁻¹‖ ≤ M * (1 + ‖x‖) ^ N)
    (hg : g.HasTemperateGrowth) : (fun x => g x / E x).HasTemperateGrowth := by
  have hEd : Differentiable ℝ E := hE.1.differentiable (by simp)
  refine hasTemperateGrowth_of_closed
    {f | ∃ (m : ℕ) (u : ℝ → ℂ), u.HasTemperateGrowth ∧ f = fun x => u x / E x ^ m} ?_ ?_ ?_
    ⟨1, g, hg, by simp⟩
  · rintro f ⟨m, u, hu, rfl⟩
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    exact hud.div (hEd.pow m) fun x => pow_ne_zero _ (h0 x)
  · rintro f ⟨m, u, hu, rfl⟩
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    have hp : (fun x => E x ^ m).HasTemperateGrowth := hE.pow m
    have hpd : Differentiable ℝ (fun x => E x ^ m) := hp.1.differentiable (by simp)
    refine ⟨m * 2, fun x => deriv u x * E x ^ m - u x * deriv (fun x => E x ^ m) x,
      ((hasTemperateGrowth_deriv hu).mul hp).sub (hu.mul (hasTemperateGrowth_deriv hp)), ?_⟩
    funext x
    rw [pow_mul]
    exact deriv_fun_div (hud x) (hpd x) (pow_ne_zero _ (h0 x))
  · rintro f ⟨m, u, hu, rfl⟩
    obtain ⟨k, C, h⟩ := hu.2 0
    refine ⟨k + N * m, C * M ^ m, fun x => ?_⟩
    have h1 : ‖u x‖ ≤ C * (1 + ‖x‖) ^ k := by simpa using h x
    have h2 := hM x
    have h3 : 0 ≤ C * (1 + ‖x‖) ^ k := (norm_nonneg _).trans h1
    calc ‖u x / E x ^ m‖ = ‖u x‖ * ‖(E x)⁻¹‖ ^ m := by
          rw [div_eq_mul_inv, norm_mul, ← inv_pow, norm_pow]
      _ ≤ (C * (1 + ‖x‖) ^ k) * (M * (1 + ‖x‖) ^ N) ^ m := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

/- English proof (translation)
Use `hasTemperateGrowth_of_closed {f | ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖G z‖ ≤ C) ∧ f = fun t : ℝ => G t} ?_ ?_ ?_ ⟨F, hF, hb, rfl⟩` and prove the remaining obligations. Introduce and unpack `f ⟨G, hG, -, rfl⟩ x`. Conclude with `(hG x).hasDerivAt.comp_ofReal.differentiableAt`. Introduce and unpack `f ⟨G, hG, hB, rfl⟩`. Use `⟨deriv G, hG.deriv, fun R => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨C, hC⟩` from `hB (R + 1)`. Use `⟨C / 1, fun z hz => ?_⟩` and prove the remaining obligations. Use `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hG.diffContOnCl ?_` and prove the remaining obligations. Introduce `w hw`. Apply `hC` to reduce the goal to its premises.

Establish `h1 : ‖w - z‖ = 1` using `by simpa [dist_eq_norm] using hw`. Establish `h2` using `Complex.abs_im_le_norm (w - z)`. Rewrite `h2` using `[Complex.sub_im, h1]`. Establish `h3` using `abs_add_le (w.im - z.im) z.im`. Rewrite `h3` using `[sub_add_cancel]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use function extensionality and compare the values at `x`. Conclude with `(hG x).hasDerivAt.comp_ofReal.deriv`. Introduce and unpack `f ⟨G, -, hB, rfl⟩`. Take `⟨C, hC⟩` from `hB 0`.

Conclude with `⟨0, C, fun x => by simpa using hC x (by simp)⟩`.
-/
theorem hasTemperateGrowth_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖F z‖ ≤ C) :
    (fun t : ℝ => F t).HasTemperateGrowth := by
  refine hasTemperateGrowth_of_closed
    {f | ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖G z‖ ≤ C) ∧
      f = fun t : ℝ => G t} ?_ ?_ ?_ ⟨F, hF, hb, rfl⟩
  · rintro f ⟨G, hG, -, rfl⟩ x
    exact (hG x).hasDerivAt.comp_ofReal.differentiableAt
  · rintro f ⟨G, hG, hB, rfl⟩
    refine ⟨deriv G, hG.deriv, fun R => ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hB (R + 1)
      refine ⟨C / 1, fun z hz => ?_⟩
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hG.diffContOnCl ?_
      intro w hw
      apply hC
      have h1 : ‖w - z‖ = 1 := by simpa [dist_eq_norm] using hw
      have h2 := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, h1] at h2
      have h3 := abs_add_le (w.im - z.im) z.im
      rw [sub_add_cancel] at h3
      linarith
    · funext x
      exact (hG x).hasDerivAt.comp_ofReal.deriv
  · rintro f ⟨G, -, hB, rfl⟩
    obtain ⟨C, hC⟩ := hB 0
    exact ⟨0, C, fun x => by simpa using hC x (by simp)⟩

noncomputable def quot (a : ℝ) : ℂ → ℂ := dslope (fun z => Complex.exp (Complex.I * (a * z))) 0

/- English proof (translation)
Use `sub_smul_dslope (fun z : ℂ => Complex.exp (Complex.I * (a * z))) 0 z` as an intermediate fact. Simplify `this` using `[quot]`.
-/
theorem mul_quot (a : ℝ) (z : ℂ) : z * quot a z = Complex.exp (Complex.I * (a * z)) - 1 := by
  have := sub_smul_dslope (fun z : ℂ => Complex.exp (Complex.I * (a * z))) 0 z
  simpa [quot] using this

/- English proof (translation)
Establish `h : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * (a * z))) (Complex.exp (Complex.I * (a * 0)) * (Complex.I * (a * 1))) 0` using `(((hasDerivAt_id (0 : ℂ)).const_mul (a : ℂ)).const_mul Complex.I).cexp`. Rewrite using `[quot, dslope_same, h.deriv]`. Simplify using the standard rewrite rules.
-/
theorem quot_zero (a : ℝ) : quot a 0 = Complex.I * a := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * (a * z)))
      (Complex.exp (Complex.I * (a * 0)) * (Complex.I * (a * 1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (a : ℂ)).const_mul Complex.I).cexp
  rw [quot, dslope_same, h.deriv]; simp

/- English proof (translation)
Rewrite using `[← differentiableOn_univ, quot, Complex.differentiableOn_dslope Filter.univ_mem]`. Use `fun_prop`.
-/
theorem differentiable_quot (a : ℝ) : Differentiable ℂ (quot a) := by
  rw [← differentiableOn_univ, quot, Complex.differentiableOn_dslope Filter.univ_mem]
  fun_prop

/- English proof (translation)
Use `hasTemperateGrowth_of_entire (differentiable_quot a) fun R => ?_` and prove the remaining obligations. Take `⟨C, hC⟩` from `(isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn (differentiable_quot a).continuous.continuousOn`. Use `⟨max C (Real.exp (|a| * R) + 1), fun z hz => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : ‖z‖ ≤ 1`. Conclude with `(hC z (by simpa using h)).trans (le_max_left _ _)`.

Use `le_trans ?_ (le_max_right _ _) push Not at h` and prove the remaining obligations. Establish `h1 : ‖z‖ * ‖quot a z‖ ≤ Real.exp (|a| * R) + 1`. Rewrite using `[← norm_mul, mul_quot]`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Complex.norm_exp, norm_one]`.

Use `gcongr`. Establish `: (Complex.I * (a * z)).re = -(a * z.im)` using `by simp`. Rewrite using `[this]`. Use `(neg_le_abs _).trans ?_` and prove the remaining obligations. Rewrite using `[abs_mul]`.

Use `gcongr`. Use polynomial arithmetic with `[norm_nonneg (quot a z)]`.
-/
theorem hasTemperateGrowth_quot (a : ℝ) : (fun t : ℝ => quot a t).HasTemperateGrowth := by
  refine hasTemperateGrowth_of_entire (differentiable_quot a) fun R => ?_
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_quot a).continuous.continuousOn
  refine ⟨max C (Real.exp (|a| * R) + 1), fun z hz => ?_⟩
  by_cases h : ‖z‖ ≤ 1
  · exact (hC z (by simpa using h)).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    push Not at h
    have h1 : ‖z‖ * ‖quot a z‖ ≤ Real.exp (|a| * R) + 1 := by
      rw [← norm_mul, mul_quot]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp, norm_one]
      gcongr
      have : (Complex.I * (a * z)).re = -(a * z.im) := by simp
      rw [this]
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      gcongr
    nlinarith [norm_nonneg (quot a z)]

/- English proof (translation)
Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using `[quot_zero]`. Establish `ht' : (t : ℂ) ≠ 0` using `by exact_mod_cast ht`. Apply `mul_left_cancel₀ ht'` to reduce the goal to its premises.

Use `congrArg (starRingEnd ℂ) (mul_quot a t)` as an intermediate fact. Rewrite `this` using `[map_mul, Complex.conj_ofReal]`. Rewrite using `[this, mul_quot, map_sub, ← Complex.exp_conj]`. Simplify using the standard rewrite rules.
-/
theorem quot_neg (a t : ℝ) : quot (-a) t = (starRingEnd ℂ) (quot a t) := by
  by_cases ht : t = 0
  · subst ht; simp [quot_zero]
  · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    apply mul_left_cancel₀ ht'
    have := congrArg (starRingEnd ℂ) (mul_quot a t)
    rw [map_mul, Complex.conj_ofReal] at this
    rw [this, mul_quot, map_sub, ← Complex.exp_conj]
    simp

/- English proof (translation)
Establish `h1 : Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) = Complex.exp (Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ))`. Establish `: Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) = Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ) + (round x : ℤ) * (2 * Real.pi * Complex.I)` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]`. Rewrite using `[h1, Complex.norm_exp_I_mul_ofReal_sub_one]`. Establish `h2` using `abs_sub_round x`.

Use `set d := x - round x`. Establish `hp` using `Real.pi_pos`. Establish `e : 2 * Real.pi * d / 2 = Real.pi * d` using `by ring`. Establish `h3 : |Real.pi * d| ≤ Real.pi / 2`. Rewrite using `[abs_mul, abs_of_pos hp]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h4` using `Real.mul_abs_le_abs_sin h3`. Rewrite `h4` using `[abs_mul, abs_of_pos hp]`. Establish `e2 : 2 / Real.pi * (Real.pi * |d|) = 2 * |d|` using `by field_simp`. Rewrite `h4` using `[e2]`.

Rewrite using `[e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_exp_sub_one_ge (x : ℝ) :
    4 * |x - round x| ≤ ‖Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := by
  have h1 : Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ)) := by
    have : Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ) + (round x : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h2 := abs_sub_round x
  set d := x - round x
  have hp := Real.pi_pos
  have e : 2 * Real.pi * d / 2 = Real.pi * d := by ring
  have h3 : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hp]; nlinarith
  have h4 := Real.mul_abs_le_abs_sin h3
  rw [abs_mul, abs_of_pos hp] at h4
  have e2 : 2 / Real.pi * (Real.pi * |d|) = 2 * |d| := by field_simp
  rw [e2] at h4
  rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  linarith

/- English proof (translation)
Use `set p := round t with hpdef`. Use `set q := round (√2 * t) with hqdef`. Establish `h1 : |t - p| ≤ 1 / 2` using `abs_sub_round t`. Establish `h2 : |√2 * t - q| ≤ 1 / 2` using `abs_sub_round _`. Establish `hs : √2 * √2 = 2` using `Real.mul_self_sqrt (by norm_num)`.

Establish `hs0 : 0 < √2` using `by positivity`. Establish `hs2 : √2 ≤ 3 / 2` using `by nlinarith`. Establish `hne : (2 * p ^ 2 - q ^ 2 : ℤ) ≠ 0`. Introduce `h`. Establish `hr : (2 : ℝ) * p ^ 2 - q ^ 2 = 0` using `by exact_mod_cast h`.

Establish `hp' : (p : ℝ) ≠ 0` using `by exact_mod_cast hp`. Establish `: (√2 * p - q) * (√2 * p + q) = 0` using `by nlinarith`. Establish `hirr` using `irrational_sqrt_two`. Break down `mul_eq_zero.1 this with h' | h'` into its components or cases. Conclude with `hirr ⟨(q : ℚ) / p, by push_cast; field_simp; linarith⟩`.

Conclude with `hirr ⟨-(q : ℚ) / p, by push_cast; field_simp; linarith⟩`. Establish `h3 : (1 : ℝ) ≤ |(2 : ℝ) * p ^ 2 - q ^ 2|`. Use `Int.one_le_abs hne` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `h4 : (2 : ℝ) * p ^ 2 - q ^ 2 = (√2 * p - q) * (√2 * p + q)` using `by nlinarith`.

Rewrite `h3` using `[h4, abs_mul]`. Establish `h5 : |√2 * p - q| ≤ 2 * (|t - p| + |√2 * t - q|)`. Establish `: √2 * p - q = (√2 * t - q) - √2 * (t - p)` using `by ring`. Rewrite using `[this]`. Use `(abs_sub _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[abs_mul, abs_of_pos hs0]`. Use polynomial arithmetic with `[abs_nonneg (t - p), abs_nonneg (√2 * t - q)]`. Establish `h6 : |√2 * p + q| ≤ 3 * (1 + |t|)`. Establish `: √2 * p + q = 2 * √2 * t - (√2 * t - q) - √2 * (t - p)` using `by ring`. Rewrite using `[this]`.

Use `(abs_sub _ _).trans ?_` and prove the remaining obligations. Use `abs_sub (2 * √2 * t) (√2 * t - q)` as an intermediate fact. Rewrite `this` using `[abs_mul, abs_mul, abs_of_pos hs0, abs_two]`. Rewrite using `[abs_mul, abs_of_pos hs0]`. Use polynomial arithmetic with `[abs_nonneg (t - p), abs_nonneg t]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem dioph (t : ℝ) (hp : round t ≠ 0) :
    1 ≤ 6 * (1 + |t|) * (|t - round t| + |√2 * t - round (√2 * t)|) := by
  set p := round t with hpdef
  set q := round (√2 * t) with hqdef
  have h1 : |t - p| ≤ 1 / 2 := abs_sub_round t
  have h2 : |√2 * t - q| ≤ 1 / 2 := abs_sub_round _
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hs2 : √2 ≤ 3 / 2 := by nlinarith
  have hne : (2 * p ^ 2 - q ^ 2 : ℤ) ≠ 0 := by
    intro h
    have hr : (2 : ℝ) * p ^ 2 - q ^ 2 = 0 := by exact_mod_cast h
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have : (√2 * p - q) * (√2 * p + q) = 0 := by nlinarith
    have hirr := irrational_sqrt_two
    rcases mul_eq_zero.1 this with h' | h'
    · exact hirr ⟨(q : ℚ) / p, by push_cast; field_simp; linarith⟩
    · exact hirr ⟨-(q : ℚ) / p, by push_cast; field_simp; linarith⟩
  have h3 : (1 : ℝ) ≤ |(2 : ℝ) * p ^ 2 - q ^ 2| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  have h4 : (2 : ℝ) * p ^ 2 - q ^ 2 = (√2 * p - q) * (√2 * p + q) := by nlinarith
  rw [h4, abs_mul] at h3
  have h5 : |√2 * p - q| ≤ 2 * (|t - p| + |√2 * t - q|) := by
    have : √2 * p - q = (√2 * t - q) - √2 * (t - p) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (t - p), abs_nonneg (√2 * t - q)]
  have h6 : |√2 * p + q| ≤ 3 * (1 + |t|) := by
    have : √2 * p + q = 2 * √2 * t - (√2 * t - q) - √2 * (t - p) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    have := abs_sub (2 * √2 * t) (√2 * t - q)
    rw [abs_mul, abs_mul, abs_of_pos hs0, abs_two] at this
    rw [abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (t - p), abs_nonneg t]
  calc (1 : ℝ) ≤ _ := h3
    _ ≤ (2 * (|t - p| + |√2 * t - q|)) * (3 * (1 + |t|)) := by gcongr
    _ = _ := by ring

/- English proof (translation)
Establish `a0` using `abs_nonneg t`. Establish `n1` using `norm_nonneg (quot (2 * Real.pi) t)`. Establish `n2` using `norm_nonneg (quot (2 * Real.pi * √2) t)`. Establish `e1 : 4 * |t - round t| ≤ |t| * ‖quot (2 * Real.pi) t‖`. Use `norm_exp_sub_one_ge t` as an intermediate fact.

Rewrite `this` using `[Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Then use the resulting hypothesis. Establish `e2 : 4 * |√2 * t - round (√2 * t)| ≤ |t| * ‖quot (2 * Real.pi * √2) t‖`. Use `norm_exp_sub_one_ge (√2 * t)` as an intermediate fact. Rewrite `this` using `[← mul_assoc, Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Then use the resulting hypothesis. Distinguish the cases in `hp : round t = 0`.

Establish `h1 : 1 ≤ ‖quot (2 * Real.pi) t‖`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Rewrite using `[Complex.ofReal_zero, quot_zero, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`. Combine the linear relations using `[Real.pi_gt_three]`.

Rewrite `e1` using `[hp]`. Simplify using `only [Int.cast_zero, sub_zero] at e1`. Establish `: 0 < |t|` using `abs_pos.2 ht`. Assume the negation of the conclusion as `hh`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2 : 1 ≤ (1 + |t|) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `h` using `dioph t hp set s := ‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖ with hs`. Establish `hs0 : 0 ≤ s` using `by positivity`. Establish `h1 : 4 * (|t - round t| + |√2 * t - round (√2 * t)|) ≤ (1 + |t|) * s`.

Rewrite using `[hs]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2` using `mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + |t| by positivity)`. Establish `h3 : 0 ≤ (1 + |t|) ^ 2 * s` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lower (t : ℝ) :
    1 ≤ 2 * (1 + |t|) ^ 2 * (‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖) := by
  have a0 := abs_nonneg t
  have n1 := norm_nonneg (quot (2 * Real.pi) t)
  have n2 := norm_nonneg (quot (2 * Real.pi * √2) t)
  have e1 : 4 * |t - round t| ≤ |t| * ‖quot (2 * Real.pi) t‖ := by
    have := norm_exp_sub_one_ge t
    rwa [Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
  have e2 : 4 * |√2 * t - round (√2 * t)| ≤ |t| * ‖quot (2 * Real.pi * √2) t‖ := by
    have := norm_exp_sub_one_ge (√2 * t)
    rwa [← mul_assoc, Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] at this
  by_cases hp : round t = 0
  · have h1 : 1 ≤ ‖quot (2 * Real.pi) t‖ := by
      by_cases ht : t = 0
      · subst ht
        rw [Complex.ofReal_zero, quot_zero, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith [Real.pi_gt_three]
      · rw [hp] at e1
        simp only [Int.cast_zero, sub_zero] at e1
        have : 0 < |t| := abs_pos.2 ht
        by_contra hh
        nlinarith
    have h2 : 1 ≤ (1 + |t|) ^ 2 := by nlinarith
    nlinarith
  · have h := dioph t hp
    set s := ‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖ with hs
    have hs0 : 0 ≤ s := by positivity
    have h1 : 4 * (|t - round t| + |√2 * t - round (√2 * t)|) ≤ (1 + |t|) * s := by
      rw [hs]; nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + |t| by positivity)
    have h3 : 0 ≤ (1 + |t|) ^ 2 * s := by positivity
    nlinarith

/- English proof (translation)
Use `set a : ℝ := 2 * Real.pi with ha`. Use `set b : ℝ := 2 * Real.pi * √2 with hb`. Use `set E : ℝ → ℂ := fun t => quot a t * quot (-a) t + quot b t * quot (-b) t with hE`. Establish `hEt : E.HasTemperateGrowth` using `((hasTemperateGrowth_quot a).mul (hasTemperateGrowth_quot (-a))).add ((hasTemperateGrowth_quot b).mul (hasTemperateGrowth_quot (-b)))`. Establish `hn : ∀ t, ‖E t‖ = ‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2`.

Introduce `t`. Establish `: E t = ((‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 : ℝ) : ℂ)`. Simplify using `only [hE, quot_neg, Complex.mul_conj']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Establish `hl : ∀ t, 1 ≤ 8 * (1 + ‖t‖) ^ 4 * ‖E t‖`. Introduce `t`. Establish `h` using `lower t`. Rewrite `h` using `[← ha, ← hb]`.

Rewrite using `[hn, Real.norm_eq_abs]`. Establish `h2` using `one_le_pow₀ (n := 2) h`. Establish `h3 : (‖quot a t‖ + ‖quot b t‖) ^ 2 ≤ 2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2)`. Use polynomial arithmetic with `[sq_nonneg (‖quot a t‖ - ‖quot b t‖)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h0 : ∀ t, E t ≠ 0`. Introduce `t h`. Use `hl t` as an intermediate fact. Rewrite `this` using `[h]`. Evaluate the numerical expressions using `at this`.

Establish `hM : ∀ t, ‖(E t)⁻¹‖ ≤ 8 * (1 + ‖t‖) ^ 4`. Introduce `t`. Rewrite using `[norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.2 (h0 t))]`. Conclude with `hl t`. Use `⟨2, ![a, b], ![fun t => quot (-a) t / E t, fun t => quot (-b) t / E t], ?_, ?_⟩` and prove the remaining obligations.

Introduce `j fin_cases j`. Conclude with `hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)`. Conclude with `hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)`. Introduce `t`. Rewrite using `[Fin.sum_univ_two]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`. Rewrite using `[Complex.ofReal_mul a t, Complex.ofReal_mul b t, ← mul_quot, ← mul_quot]`. Use `h0 t` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Simplify using `only [hE]`.
-/
theorem exists_division : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ),
    (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  set a : ℝ := 2 * Real.pi with ha
  set b : ℝ := 2 * Real.pi * √2 with hb
  set E : ℝ → ℂ := fun t => quot a t * quot (-a) t + quot b t * quot (-b) t with hE
  have hEt : E.HasTemperateGrowth :=
    ((hasTemperateGrowth_quot a).mul (hasTemperateGrowth_quot (-a))).add
      ((hasTemperateGrowth_quot b).mul (hasTemperateGrowth_quot (-b)))
  have hn : ∀ t, ‖E t‖ = ‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 := by
    intro t
    have : E t = ((‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 : ℝ) : ℂ) := by
      simp only [hE, quot_neg, Complex.mul_conj']
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hl : ∀ t, 1 ≤ 8 * (1 + ‖t‖) ^ 4 * ‖E t‖ := by
    intro t
    have h := lower t
    rw [← ha, ← hb] at h
    rw [hn, Real.norm_eq_abs]
    have h2 := one_le_pow₀ (n := 2) h
    have h3 : (‖quot a t‖ + ‖quot b t‖) ^ 2 ≤ 2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2) := by
      nlinarith [sq_nonneg (‖quot a t‖ - ‖quot b t‖)]
    calc (1 : ℝ) ≤ _ := h2
      _ = 4 * (1 + |t|) ^ 4 * (‖quot a t‖ + ‖quot b t‖) ^ 2 := by ring
      _ ≤ 4 * (1 + |t|) ^ 4 * (2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2)) := by gcongr
      _ = _ := by ring
  have h0 : ∀ t, E t ≠ 0 := by
    intro t h
    have := hl t
    rw [h] at this
    norm_num at this
  have hM : ∀ t, ‖(E t)⁻¹‖ ≤ 8 * (1 + ‖t‖) ^ 4 := by
    intro t
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.2 (h0 t))]
    exact hl t
  refine ⟨2, ![a, b], ![fun t => quot (-a) t / E t, fun t => quot (-b) t / E t], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)
    · exact hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)
  · intro t
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Complex.ofReal_mul a t, Complex.ofReal_mul b t, ← mul_quot, ← mul_quot]
    have := h0 t
    field_simp
    simp only [hE]

end GlobalTheory.ExpDivision
