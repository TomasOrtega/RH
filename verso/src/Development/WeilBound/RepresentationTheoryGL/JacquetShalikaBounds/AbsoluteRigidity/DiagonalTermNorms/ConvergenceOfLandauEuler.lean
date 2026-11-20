import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

noncomputable section

open scoped ComplexConjugate

namespace PositivityTheory.RgJS

namespace DiagonalEntryNormBounds

variable {W : Type} (q : W → ℕ)

def ll (p : W × ℕ) : ℝ := ((p.2 : ℝ) + 1) * Real.log (q p.1)

/- English proof (translation)
Unfold `ll`. Establish `h1 : (1 : ℝ) ≤ q p.1` using `by exact_mod_cast (le_trans (by norm_num) (hq p.1))`. Conclude with `mul_nonneg (by positivity) (Real.log_nonneg h1)`.
-/
theorem ll_nonneg (hq : ∀ w, 2 ≤ q w) (p : W × ℕ) : 0 ≤ ll q p := by
  unfold ll
  have h1 : (1 : ℝ) ≤ q p.1 := by exact_mod_cast (le_trans (by norm_num) (hq p.1))
  exact mul_nonneg (by positivity) (Real.log_nonneg h1)

/- English proof (translation)
Establish `h0 : (0 : ℝ) < q p.1` using `by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul h0.le, Real.rpow_def_of_pos h0]`. Unfold `ll`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_eq_exp (hq : ∀ w, 2 ≤ q w) (σ : ℝ) (p : W × ℕ) :
    ((q p.1 : ℝ) ^ (-σ)) ^ (p.2 + 1) = Real.exp (-(ll q p * σ)) := by
  have h0 : (0 : ℝ) < q p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, Real.rpow_def_of_pos h0]
  unfold ll
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `h0 : 0 < q p.1` using `lt_of_lt_of_le (by norm_num) (hq p.1)`. Unfold `lterm`. Rewrite using `[norm_div, norm_mul, norm_mul, Complex.norm_conj, norm_pow, Complex.norm_natCast_cpow_of_pos h0, ← pow_eq_exp q hq]`. Establish `hd : ‖((p.2 : ℂ) + 1)‖ = (p.2 : ℝ) + 1`. Establish `: ((p.2 : ℂ) + 1) = (((p.2 : ℝ) + 1 : ℝ) : ℂ)` using `by push_cast; ring`.

Rewrite using `[this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Establish `hre : (-(σ : ℂ)).re = -σ` using `by simp`. Rewrite using `[hre, hd]`.
-/
theorem norm_lterm {A B : Type} [Fintype A] [Fintype B] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ) (σ : ℝ)
    (p : W × ℕ) :
    ‖lterm q α β σ p‖ = ‖∑ a, α p.1 a ^ (p.2 + 1)‖ * ‖∑ b, β p.1 b ^ (p.2 + 1)‖ * Real.exp (-(ll q p * σ)) /
      ((p.2 : ℝ) + 1) := by
  have h0 : 0 < q p.1 := lt_of_lt_of_le (by norm_num) (hq p.1)
  unfold lterm
  rw [norm_div, norm_mul, norm_mul, Complex.norm_conj, norm_pow, Complex.norm_natCast_cpow_of_pos h0, ← pow_eq_exp q hq]
  have hd : ‖((p.2 : ℂ) + 1)‖ = (p.2 : ℝ) + 1 := by
    have : ((p.2 : ℂ) + 1) = (((p.2 : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hre : (-(σ : ℂ)).re = -σ := by simp
  rw [hre, hd]

def cd {A : Type} [Fintype A] (α : W → A → ℂ) (p : W × ℕ) : ℝ := ‖∑ a, α p.1 a ^ (p.2 + 1)‖ ^ 2 / ((p.2 : ℝ) + 1)

/- English proof (translation)
Unfold `cd`. Check the signs of the components of the expression.
-/
theorem cd_nonneg {A : Type} [Fintype A] (α : W → A → ℂ) (p : W × ℕ) : 0 ≤ cd α p := by
  unfold cd; positivity

/- English proof (translation)
Establish `h0 : (0 : ℝ) < q p.1` using `by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))`. Unfold `lterm cd`. Establish `e1 : ((q p.1 : ℂ) ^ (-(σ : ℂ))) = (((q p.1 : ℝ) ^ (-σ) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_cpow h0.le]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[e1, ← Complex.ofReal_pow, pow_eq_exp q hq, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lterm_diag {A : Type} [Fintype A] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (σ : ℝ) (p : W × ℕ) :
    lterm q α α σ p = ((cd α p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  have h0 : (0 : ℝ) < q p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))
  unfold lterm cd
  have e1 : ((q p.1 : ℂ) ^ (-(σ : ℂ))) = (((q p.1 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow h0.le]; push_cast; rfl
  rw [e1, ← Complex.ofReal_pow, pow_eq_exp q hq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[lterm_diag q hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]`. Conclude with `mul_nonneg (cd_nonneg α p) (Real.exp_pos _).le`.
-/
theorem norm_lterm_diag {A : Type} [Fintype A] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (σ : ℝ) (p : W × ℕ) :
    ‖lterm q α α σ p‖ = cd α p * Real.exp (-(ll q p * σ)) := by
  rw [lterm_diag q hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (cd_nonneg α p) (Real.exp_pos _).le

/- English proof (translation)
Rewrite using `[norm_lterm q hq, norm_lterm_diag q hq, norm_lterm_diag q hq]`. Unfold `cd`. Use `set u := ‖∑ a, α p.1 a ^ (p.2 + 1)‖`. Use `set v := ‖∑ b, β p.1 b ^ (p.2 + 1)‖`. Use `set e := Real.exp (-(ll q p * σ))`.

Establish `he : 0 ≤ e` using `(Real.exp_pos _).le`. Establish `hk : (0 : ℝ) < (p.2 : ℝ) + 1` using `by positivity`. Establish `h2 : u * v ≤ (u ^ 2 + v ^ 2) / 2` using `by nlinarith [sq_nonneg (u - v)]`. Establish `e1 : (u ^ 2 / ((p.2 : ℝ) + 1) * e + v ^ 2 / ((p.2 : ℝ) + 1) * e) / 2 = ((u ^ 2 + v ^ 2) / 2 * e) / ((p.2 : ℝ) + 1)` using `by field_simp`. Rewrite using `[e1]`.

Apply `div_le_div_of_nonneg_right _ hk.le` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_right h2 he`.
-/
theorem norm_lterm_le {A B : Type} [Fintype A] [Fintype B] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ)
    (σ : ℝ) (p : W × ℕ) :
    ‖lterm q α β σ p‖ ≤ (‖lterm q α α σ p‖ + ‖lterm q β β σ p‖) / 2 := by
  rw [norm_lterm q hq, norm_lterm_diag q hq, norm_lterm_diag q hq]
  unfold cd
  set u := ‖∑ a, α p.1 a ^ (p.2 + 1)‖
  set v := ‖∑ b, β p.1 b ^ (p.2 + 1)‖
  set e := Real.exp (-(ll q p * σ))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hk : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
  have h2 : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by nlinarith [sq_nonneg (u - v)]
  have e1 : (u ^ 2 / ((p.2 : ℝ) + 1) * e + v ^ 2 / ((p.2 : ℝ) + 1) * e) / 2 =
      ((u ^ 2 + v ^ 2) / 2 * e) / ((p.2 : ℝ) + 1) := by field_simp
  rw [e1]
  apply div_le_div_of_nonneg_right _ hk.le
  exact mul_le_mul_of_nonneg_right h2 he

/- English proof (translation)
Rewrite using `[norm_lterm q hq, norm_lterm q hq]`. Establish `hk : (0 : ℝ) < (p.2 : ℝ) + 1` using `by positivity`. Apply `div_le_div_of_nonneg_right _ hk.le` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Apply `Real.exp_le_exp.2` to reduce the goal to its premises.

Use `ll_nonneg q hq p` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_lterm_anti {A B : Type} [Fintype A] [Fintype B] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ)
    {σ σ₁ : ℝ} (h : σ₁ ≤ σ) (p : W × ℕ) : ‖lterm q α β σ p‖ ≤ ‖lterm q α β σ₁ p‖ := by
  rw [norm_lterm q hq, norm_lterm q hq]
  have hk : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
  apply div_le_div_of_nonneg_right _ hk.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  have := ll_nonneg q hq p
  nlinarith

end DiagonalEntryNormBounds

open DiagonalEntryNormBounds in
/- English proof (translation)
Introduce `hL hE W q X d A hS`. Establish `hq` using `hS.primes.two`. Establish `diag : ∀ x : X, ∀ σ : ℝ, 1 < σ → Summable fun p => ‖lterm q (A x) (A x) σ p‖`. Introduce `x`. Take `⟨F, σ₀, hF, hFe⟩` from `hS.rs x x`.

Use `set σ₁ : ℝ := max σ₀ 2 with hσ₁`. Establish `hsum : ∀ σ : ℝ, σ₁ < σ → Summable fun p => cd (A x) p * Real.exp (-(ll q p * σ))`. Introduce `σ hσ`. Establish `h2 : 2 < (σ : ℂ).re` using `by simp; exact lt_of_le_of_lt (le_max_right _ _) hσ`. Use `(hE W q _ _ (A x) (A x) σ hS.primes (hS.bd x) (hS.bd x) h2).1` as an intermediate fact.

Conclude with `this.congr fun p => norm_lterm_diag q hq (A x) σ p`. Establish `key` using `hL (W × ℕ) (cd (A x)) (ll q) 1 σ₁ (fun s => F s / (s - 1)) (cd_nonneg (A x)) (ll_nonneg q hq) (fun σ hσ => by`. Establish `h1 : ((σ : ℂ) - 1) ≠ 0`. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact.

Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hF σ (by linarith)).div (analyticAt_id.sub analyticAt_const) h1)`. Use `hsum`. Use the proof step `(fun σ hσ => by`.

Establish `hσ0 : σ₀ < σ` using `lt_of_le_of_lt (le_max_left _ _) hσ`. Establish `h2 : 2 < (σ : ℂ).re` using `by simp; exact lt_of_le_of_lt (le_max_right _ _) hσ`. Establish `h1 : ((σ : ℂ) - 1) ≠ 0`. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact.

Simplify using `at this`. Combine the linear relations using `[le_max_right σ₀ 2]`. Rewrite using `[hFe σ hσ0, if_pos rfl, mul_div_cancel_left₀ _ h1, (hE W q _ _ (A x) (A x) σ hS.primes (hS.bd x) (hS.bd x) h2).2.1]`. Establish `e : (∑' p, lterm q (A x) (A x) (σ : ℂ) p) = ((∑' p, cd (A x) p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_tsum]`.

Conclude with `tsum_congr fun p => lterm_diag q hq (A x) σ p`. Rewrite using `[e, ← Complex.ofReal_exp])`. Introduce `σ hσ`. Conclude with `(key σ hσ).congr fun p => (norm_lterm_diag q hq (A x) σ p).symm`. Establish `all : ∀ x y : X, ∀ σ : ℝ, 1 < σ → Summable fun p => ‖lterm q (A x) (A y) σ p‖`.

Introduce `x y σ hσ`. Use `Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_lterm_le q hq (A x) (A y) σ p) ?_` and prove the remaining obligations. Conclude with `((diag x σ hσ).add (diag y σ hσ)).div_const 2`. Introduce `x y`. Use `⟨all x y, fun σ₁ hσ₁ => ⟨∑' p, ‖lterm q (A x) (A y) σ₁ p‖, fun σ hσ => ?_⟩⟩` and prove the remaining obligations.

Use `(norm_tsum_le_tsum_norm (all x y σ (by linarith))).trans ?_` and prove the remaining obligations. Conclude with `(all x y σ (by linarith)).tsum_le_tsum (fun p => norm_lterm_anti q hq (A x) (A y) hσ p) (all x y σ₁ hσ₁)`.
-/
theorem convergence_of_landau_euler : LandauL → EulerLog → Conv1 := by
  intro hL hE W q X d A hS
  have hq := hS.primes.two

  have diag : ∀ x : X, ∀ σ : ℝ, 1 < σ → Summable fun p => ‖lterm q (A x) (A x) σ p‖ := by
    intro x
    obtain ⟨F, σ₀, hF, hFe⟩ := hS.rs x x
    set σ₁ : ℝ := max σ₀ 2 with hσ₁
    have hsum : ∀ σ : ℝ, σ₁ < σ → Summable fun p => cd (A x) p * Real.exp (-(ll q p * σ)) := by
      intro σ hσ
      have h2 : 2 < (σ : ℂ).re := by simp; exact lt_of_le_of_lt (le_max_right _ _) hσ
      have := (hE W q _ _ (A x) (A x) σ hS.primes (hS.bd x) (hS.bd x) h2).1
      exact this.congr fun p => norm_lterm_diag q hq (A x) σ p
    have key := hL (W × ℕ) (cd (A x)) (ll q) 1 σ₁ (fun s => F s / (s - 1)) (cd_nonneg (A x)) (ll_nonneg q hq)
      (fun σ hσ => by
        have h1 : ((σ : ℂ) - 1) ≠ 0 := by
          intro h; have := congrArg Complex.re h; simp at this; linarith
        exact (hF σ (by linarith)).div (analyticAt_id.sub analyticAt_const) h1)
      hsum
      (fun σ hσ => by
        have hσ0 : σ₀ < σ := lt_of_le_of_lt (le_max_left _ _) hσ
        have h2 : 2 < (σ : ℂ).re := by simp; exact lt_of_le_of_lt (le_max_right _ _) hσ
        have h1 : ((σ : ℂ) - 1) ≠ 0 := by
          intro h; have := congrArg Complex.re h; simp at this; linarith [le_max_right σ₀ 2]
        rw [hFe σ hσ0, if_pos rfl, mul_div_cancel_left₀ _ h1,
          (hE W q _ _ (A x) (A x) σ hS.primes (hS.bd x) (hS.bd x) h2).2.1]
        have e : (∑' p, lterm q (A x) (A x) (σ : ℂ) p) = ((∑' p, cd (A x) p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_tsum]
          exact tsum_congr fun p => lterm_diag q hq (A x) σ p
        rw [e, ← Complex.ofReal_exp])
    intro σ hσ
    exact (key σ hσ).congr fun p => (norm_lterm_diag q hq (A x) σ p).symm
  have all : ∀ x y : X, ∀ σ : ℝ, 1 < σ → Summable fun p => ‖lterm q (A x) (A y) σ p‖ := by
    intro x y σ hσ
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_lterm_le q hq (A x) (A y) σ p) ?_
    exact ((diag x σ hσ).add (diag y σ hσ)).div_const 2
  intro x y
  refine ⟨all x y, fun σ₁ hσ₁ => ⟨∑' p, ‖lterm q (A x) (A y) σ₁ p‖, fun σ hσ => ?_⟩⟩
  refine (norm_tsum_le_tsum_norm (all x y σ (by linarith))).trans ?_
  exact (all x y σ (by linarith)).tsum_le_tsum (fun p => norm_lterm_anti q hq (A x) (A y) hσ p) (all x y σ₁ hσ₁)

end PositivityTheory.RgJS
