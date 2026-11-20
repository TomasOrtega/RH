import Mathlib
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨?_, (hasSum_fintype _).summable⟩` and prove the remaining obligations. Simplify using `using hasSum_fintype (fun f : Fin 0 → ι => ∏ k, z (f k))`. Consider the case `succ n ih`.

Take `⟨ih₁, ih₂⟩` from `ih`. Set `e : (ι × (Fin n → ι)) ≃ (Fin (n + 1) → ι)` to `Fin.consEquiv (fun _ : Fin (n + 1) => ι)`. Establish `key : ∀ x : ι × (Fin n → ι), (∏ k, z (e x k)) = z x.1 * ∏ k, z (x.2 k)`. Introduce `x`. Express the relevant statement in the definitionally equal form `∏ k, z ((Fin.cons x.1 x.2 : Fin (n + 1) → ι) k) = _`.

Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Establish `hfun : (fun f : Fin (n + 1) → ι => ∏ k, z (f k)) ∘ e = fun x : ι × (Fin n → ι) => z x.1 * ∏ k, z (x.2 k)` using `funext key`. Establish `hnorm : (fun f : Fin (n + 1) → ι => ‖∏ k, z (f k)‖) ∘ e = fun x : ι × (Fin n → ι) => ‖z x.1‖ * ‖∏ k, z (x.2 k)‖`. Use function extensionality and compare the values at `x`.

Rewrite using `[← norm_mul, ← key x]`. Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `H : HasSum (fun x : ι × (Fin n → ι) => z x.1 * ∏ k, z (x.2 k)) (g * g ^ n)` using `HasSum.mul (f := z) (g := fun f : Fin n → ι => ∏ k, z (f k)) h ih₁ (summable_mul_of_summable_norm (f := z) (g := fun f : Fin n → ι => ∏ k, z (f k)) hz ih₂)`. Rewrite `H` using `[← hfun]`.

Rewrite using `[pow_succ']`. Conclude with `(Equiv.hasSum_iff e).mp H`. Establish `H : Summable (fun x : ι × (Fin n → ι) => ‖z x.1‖ * ‖∏ k, z (x.2 k)‖)` using `Summable.mul_of_nonneg (f := fun i => ‖z i‖) (g := fun f : Fin n → ι => ‖∏ k, z (f k)‖) hz ih₂ (fun i => norm_nonneg (z i)) (fun f => norm_nonneg _)`. Rewrite `H` using `[← hnorm]`. Conclude with `(Equiv.summable_iff e).mp H`.
-/
private theorem hasSum_prod_fin_pow {ι : Type} (z : ι → ℂ) (g : ℂ)
    (hz : Summable fun i => ‖z i‖) (h : HasSum z g) (n : ℕ) :
    HasSum (fun f : Fin n → ι => ∏ k, z (f k)) (g ^ n) ∧
      Summable fun f : Fin n → ι => ‖∏ k, z (f k)‖ := by
  induction n with
  | zero =>
    refine ⟨?_, (hasSum_fintype _).summable⟩
    simpa using hasSum_fintype (fun f : Fin 0 → ι => ∏ k, z (f k))
  | succ n ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    let e : (ι × (Fin n → ι)) ≃ (Fin (n + 1) → ι) := Fin.consEquiv (fun _ : Fin (n + 1) => ι)
    have key : ∀ x : ι × (Fin n → ι), (∏ k, z (e x k)) = z x.1 * ∏ k, z (x.2 k) := by
      intro x
      change ∏ k, z ((Fin.cons x.1 x.2 : Fin (n + 1) → ι) k) = _
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hfun : (fun f : Fin (n + 1) → ι => ∏ k, z (f k)) ∘ e =
        fun x : ι × (Fin n → ι) => z x.1 * ∏ k, z (x.2 k) := funext key
    have hnorm : (fun f : Fin (n + 1) → ι => ‖∏ k, z (f k)‖) ∘ e =
        fun x : ι × (Fin n → ι) => ‖z x.1‖ * ‖∏ k, z (x.2 k)‖ := by
      funext x
      rw [← norm_mul, ← key x]
      rfl
    refine ⟨?_, ?_⟩
    · have H : HasSum (fun x : ι × (Fin n → ι) => z x.1 * ∏ k, z (x.2 k)) (g * g ^ n) :=
        HasSum.mul (f := z) (g := fun f : Fin n → ι => ∏ k, z (f k)) h ih₁
          (summable_mul_of_summable_norm (f := z) (g := fun f : Fin n → ι => ∏ k, z (f k)) hz ih₂)
      rw [← hfun] at H
      rw [pow_succ']
      exact (Equiv.hasSum_iff e).mp H
    · have H : Summable (fun x : ι × (Fin n → ι) => ‖z x.1‖ * ‖∏ k, z (x.2 k)‖) :=
        Summable.mul_of_nonneg (f := fun i => ‖z i‖) (g := fun f : Fin n → ι => ‖∏ k, z (f k)‖)
          hz ih₂ (fun i => norm_nonneg (z i)) (fun f => norm_nonneg _)
      rw [← hnorm] at H
      exact (Equiv.summable_iff e).mp H

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in

/- English proof (translation)
Establish `hz : Summable fun i => ‖z i‖` using `summable_norm_iff.mpr h.summable`. Establish `hz' : HasSum (fun i => ((‖z i‖ : ℝ) : ℂ)) ((∑' i, ‖z i‖ : ℝ) : ℂ)` using `Complex.hasSum_ofReal.mpr hz.hasSum`. Establish `hzn : Summable fun i => ‖((‖z i‖ : ℝ) : ℂ)‖`. Simplify using `using hz`. Establish `fibr : ∀ n, HasSum (fun f : Fin n → ι => ‖∏ k, z (f k)‖) ((∑' i, ‖z i‖) ^ n)`.

Introduce `n`. Establish `h1` using `(hasSum_prod_fin_pow _ _ hzn hz' n).1`. Establish `h2 : (fun f : Fin n → ι => ∏ k, ((‖z (f k)‖ : ℝ) : ℂ)) = fun f => ((‖∏ k, z (f k)‖ : ℝ) : ℂ)`. Use function extensionality and compare the values at `f`. Rewrite using `[norm_prod, Complex.ofReal_prod]`.

Rewrite `h1` using `[h2, ← Complex.ofReal_pow]`. Conclude with `Complex.hasSum_ofReal.mp h1`. Establish `hsum : Summable fun p : (Σ n : ℕ, Fin n → ι) => (∏ k, z (p.2 k)) / (p.1.factorial : ℂ)`. Apply `Summable.of_norm` to reduce the goal to its premises. Rewrite using `[summable_sigma_of_nonneg (fun _ => norm_nonneg _)]`.

Use `⟨fun n => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [norm_div, Complex.norm_natCast]`. Conclude with `(fibr n).summable.div_const _`. Simplify using `only [norm_div, Complex.norm_natCast]`. Establish `hn : ∀ n : ℕ, ∑' f : Fin n → ι, ‖∏ k, z (f k)‖ / (n.factorial : ℝ) = (∑' i, ‖z i‖) ^ n / n.factorial` using `fun n => ((fibr n).div_const _).tsum_eq`.

Simplify using `only [hn]`. Conclude with `Real.summable_pow_div_factorial _`. Establish `hexp : HasSum (fun n : ℕ => g ^ n / (n.factorial : ℂ)) (Complex.exp g)`. Rewrite using `[Complex.exp_eq_exp_ℂ]`. Conclude with `NormedSpace.expSeries_div_hasSum_exp g`.

Conclude with `HasSum.sigma_of_hasSum hexp (fun n => ((hasSum_prod_fin_pow z g hz h n).1.div_const (n.factorial : ℂ))) hsum`.
-/
theorem _root_.GlobalTheory.hasSum_tuple_prod_exp {ι : Type} (z : ι → ℂ) (g : ℂ) (h : HasSum z g) :
    HasSum (fun p : (Σ n : ℕ, Fin n → ι) => (∏ k, z (p.2 k)) / (p.1.factorial : ℂ))
      (Complex.exp g) := by
  have hz : Summable fun i => ‖z i‖ := summable_norm_iff.mpr h.summable
  have hz' : HasSum (fun i => ((‖z i‖ : ℝ) : ℂ)) ((∑' i, ‖z i‖ : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr hz.hasSum
  have hzn : Summable fun i => ‖((‖z i‖ : ℝ) : ℂ)‖ := by
    simpa using hz
  have fibr : ∀ n, HasSum (fun f : Fin n → ι => ‖∏ k, z (f k)‖) ((∑' i, ‖z i‖) ^ n) := by
    intro n
    have h1 := (hasSum_prod_fin_pow _ _ hzn hz' n).1
    have h2 : (fun f : Fin n → ι => ∏ k, ((‖z (f k)‖ : ℝ) : ℂ)) =
        fun f => ((‖∏ k, z (f k)‖ : ℝ) : ℂ) := by
      funext f
      rw [norm_prod, Complex.ofReal_prod]
    rw [h2, ← Complex.ofReal_pow] at h1
    exact Complex.hasSum_ofReal.mp h1
  have hsum : Summable fun p : (Σ n : ℕ, Fin n → ι) =>
      (∏ k, z (p.2 k)) / (p.1.factorial : ℂ) := by
    apply Summable.of_norm
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun n => ?_, ?_⟩
    · simp only [norm_div, Complex.norm_natCast]
      exact (fibr n).summable.div_const _
    · simp only [norm_div, Complex.norm_natCast]
      have hn : ∀ n : ℕ, ∑' f : Fin n → ι, ‖∏ k, z (f k)‖ / (n.factorial : ℝ) =
          (∑' i, ‖z i‖) ^ n / n.factorial := fun n => ((fibr n).div_const _).tsum_eq
      simp only [hn]
      exact Real.summable_pow_div_factorial _
  have hexp : HasSum (fun n : ℕ => g ^ n / (n.factorial : ℂ)) (Complex.exp g) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp g
  exact HasSum.sigma_of_hasSum hexp
    (fun n => ((hasSum_prod_fin_pow z g hz h n).1.div_const (n.factorial : ℂ))) hsum

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in

/- English proof (translation)
Introduce `ι a l F ha hl hF hD`. Set `b : (Σ n : ℕ, Fin n → ι) → ℝ` to `fun p => (∏ k, a (p.2 k)) / (p.1.factorial : ℝ)`. Set `L : (Σ n : ℕ, Fin n → ι) → ℝ` to `fun p => ∑ k, l (p.2 k)`. Establish `hb : ∀ p, 0 ≤ b p` using `fun p => div_nonneg (Finset.prod_nonneg fun k _ => ha _) (Nat.cast_nonneg _)`. Establish `hL : ∀ p, 0 ≤ L p` using `fun p => Finset.sum_nonneg fun k _ => hl _`.

Establish `hA : ∀ s : ℂ, 1 < s.re → HasSum (fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * s)) (F s)`. Introduce `s hs`. Take `⟨g, hg, hFg⟩` from `hD s hs`. Rewrite using `[hFg]`. Establish `H` using `_root_.GlobalTheory.hasSum_tuple_prod_exp _ g hg`.

Establish `heq : (fun p : (Σ n : ℕ, Fin n → ι) => (∏ k, (a (p.2 k) : ℂ) * Complex.exp (-(l (p.2 k) : ℂ) * s)) / (p.1.factorial : ℂ)) = fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * s)`. Use function extensionality and compare the values at `p`. Establish `hsum : ∑ k, (-(l (p.2 k) : ℂ) * s) = -(L p : ℂ) * s`. Simplify using `only [L, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_neg_distrib, neg_mul]`. Rewrite using `[Finset.prod_mul_distrib, ← Complex.exp_sum, hsum]`.

Simplify using `only [b, Complex.ofReal_div, Complex.ofReal_prod, Complex.ofReal_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `H` using `[heq]`. Conclude with `H`. Establish `hB : ∀ σ : ℝ, 1 < σ → Summable fun p => b p * Real.exp (-(L p * σ))`.

Introduce `σ hσ`. Establish `H` using `(hA σ (by simpa using hσ)).summable`. Establish `heq : (fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * (σ : ℂ))) = fun p => ((b p * Real.exp (-(L p * σ)) : ℝ) : ℂ)`. Use function extensionality and compare the values at `p`. Rewrite using `[Complex.ofReal_mul, Complex.ofReal_exp]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite `H` using `[heq]`. Conclude with `Complex.summable_ofReal.mp H`. Establish `hexpR : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x)`.

Introduce `x`. Rewrite using `[Real.exp_eq_exp_ℝ]`. Conclude with `NormedSpace.expSeries_div_hasSum_exp x`. Establish `hexpC : ∀ x : ℂ, HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ)) (Complex.exp x)`. Introduce `x`.

Rewrite using `[Complex.exp_eq_exp_ℂ]`. Conclude with `NormedSpace.expSeries_div_hasSum_exp x`. Set `T : ℝ → (Σ n : ℕ, Fin n → ι) × ℕ → ℝ` to `fun t q => b q.1 * Real.exp (-(2 * L q.1)) * ((L q.1 * t) ^ q.2 / (q.2.factorial : ℝ))`. Establish `hT : ∀ t, 0 ≤ t → ∀ q, 0 ≤ T t q`. Introduce `t ht q`.

Use `hL q.1` as an intermediate fact. Conclude with `mul_nonneg (mul_nonneg (hb _) (Real.exp_pos _).le) (by positivity)`. Establish `hfib : ∀ t p, HasSum (fun n => T t (p, n)) (b p * Real.exp (-(L p * (2 - t))))`. Introduce `t p`. Establish `H` using `(hexpR (L p * t)).mul_left (b p * Real.exp (-(2 * L p)))`.

Rewrite using `[show -(L p * (2 - t)) = -(2 * L p) + L p * t by ring, Real.exp_add, ← mul_assoc]`. Conclude with `H`. Establish `hK : ∀ t, 0 ≤ t → ∀ n, Summable fun p => T t (p, n)`. Introduce `t ht n`. Use `Summable.of_nonneg_of_le (fun p => hT t ht (p, n)) (fun p => ?_) ((hB (7 / 4) (by norm_num)).mul_left ((4 * t) ^ n))` and prove the remaining obligations.

Establish `hLp` using `hL p`. Establish `h1 : (L p * t) ^ n / (n.factorial : ℝ) = (4 * t) ^ n * ((L p / 4) ^ n / n.factorial)`. Rewrite using `[show L p * t = (4 * t) * (L p / 4) by ring, mul_pow, mul_div_assoc]`. Establish `h2 : (L p / 4) ^ n / (n.factorial : ℝ) ≤ Real.exp (L p / 4)` using `Real.pow_div_factorial_le_exp _ (by positivity) n`. Establish `h3 : b p * Real.exp (-(2 * L p)) * ((4 * t) ^ n * Real.exp (L p / 4)) = (4 * t) ^ n * (b p * Real.exp (-(L p * (7 / 4))))`.

Rewrite using `[show -(L p * (7 / 4)) = -(2 * L p) + L p / 4 by ring, Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `b p * Real.exp (-(2 * L p)) * ((L p * t) ^ n / (n.factorial : ℝ)) ≤ _`. Rewrite using `[h1, ← h3]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) n)) (mul_nonneg (hb p) (Real.exp_pos _).le)`.

Establish `hK2 : ∀ t, 0 ≤ t → t < 1 → Summable (T t)`. Introduce `t ht ht1`. Rewrite using `[summable_prod_of_nonneg (fun q => hT t ht q)]`. Use `⟨fun p => (hfib t p).summable, ?_⟩` and prove the remaining obligations. Simplify using `only [fun p => (hfib t p).tsum_eq]`.

Conclude with `hB (2 - t) (by linarith)`. Establish `hK2' : ∀ t, 0 ≤ t → t < 1 → Summable fun n => ∑' p, T t (p, n)`. Introduce `t ht ht1`. Establish `hs : Summable fun q : ℕ × (Σ n : ℕ, Fin n → ι) => T t q.swap` using `(hK2 t ht ht1).prod_symm`. Conclude with `((summable_prod_of_nonneg (fun q => hT t ht q.swap)).mp hs).2`.

Set `r : ℕ → ℝ` to `fun n => ∑' p, T 1 (p, n)`. Set `c : ℕ → ℂ` to `fun n => (-1) ^ n * (r n : ℂ)`. Establish `hr : ∀ n, 0 ≤ r n` using `fun n => tsum_nonneg fun p => hT 1 zero_le_one (p, n)`. Establish `hrad : 1 ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius`. Use `ENNReal.le_of_forall_nnreal_lt fun ρ hρ => ?_` and prove the remaining obligations.

Establish `hρ1 : (ρ : ℝ) < 1` using `by exact_mod_cast hρ`. Establish `hρ0 : (0 : ℝ) ≤ ρ` using `ρ.2`. Use `FormalMultilinearSeries.le_radius_of_bound _ (∑' m, ∑' p, T ρ (p, m)) fun n => ?_` and prove the remaining obligations. Rewrite using `[FormalMultilinearSeries.ofScalars_norm_eq_mul, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]`. Establish `hcn : ‖c n‖ = r n`.

Simplify using `only [c, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr n)]`. Establish `hrn : r n * (ρ : ℝ) ^ n = ∑' p, T ρ (p, n)`. Simplify using `only [r, ← tsum_mul_right]`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Simplify using `only [T]`. Rewrite using `[mul_pow, mul_pow, one_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcn, hrn]`. Conclude with `(hK2' ρ hρ0 hρ1).le_tsum n fun m _ => tsum_nonneg fun p => hT ρ hρ0 (p, m)`.

Establish `hps : HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℂ c) 2 1`. Use `⟨hrad, one_pos, fun {y} hy => ?_⟩` and prove the remaining obligations. Establish `hy1 : ‖y‖ < 1`. Simplify `hy` using `[EMetric.mem_ball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]`. Simplify using `only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]`.

Set `E : (Σ n : ℕ, Fin n → ι) × ℕ → ℂ` to `fun q => ((b q.1 * Real.exp (-(2 * L q.1)) : ℝ) : ℂ) * ((-(L q.1 : ℂ) * y) ^ q.2 / (q.2.factorial : ℂ))`. Establish `hEn : ∀ q, ‖E q‖ = T ‖y‖ q`. Introduce `q`. Simplify using `only [E, T, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs]`. Rewrite using `[abs_of_nonneg (hb q.1), Real.abs_exp, abs_of_nonneg (hL q.1)]`.

Establish `hEs : Summable E`. Use `Summable.of_norm ?_` and prove the remaining obligations. Simplify using `only [hEn]`. Conclude with `hK2 ‖y‖ (norm_nonneg _) hy1`. Establish `hfibE : ∀ p, HasSum (fun n => E (p, n)) ((b p : ℂ) * Complex.exp (-(L p : ℂ) * (2 + y)))`.

Introduce `p`. Establish `H` using `(hexpC (-(L p : ℂ) * y)).mul_left ((b p * Real.exp (-(2 * L p)) : ℝ) : ℂ)`. Establish `heq : ((b p * Real.exp (-(2 * L p)) : ℝ) : ℂ) * Complex.exp (-(L p : ℂ) * y) = (b p : ℂ) * Complex.exp (-(L p : ℂ) * (2 + y))`. Rewrite using `[Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]`. Use `push_cast`.

Put the polynomial expressions in normal form. Rewrite `H` using `[heq]`. Conclude with `H`. Establish `hre : 1 < (2 + y).re`. Use `Complex.abs_re_le_norm y` as an intermediate fact.

Rewrite using `[Complex.add_re]`. Evaluate the numerical expressions. Combine the linear relations using `[abs_le.mp this]`. Establish `hEsum : ∑' q, E q = F (2 + y)` using `(hEs.hasSum.prod_fiberwise hfibE).unique (hA _ hre)`. Establish `hsw : HasSum (fun q : ℕ × (Σ n : ℕ, Fin n → ι) => E q.swap) (F (2 + y))`.

Establish `ht : ∑' q : ℕ × (Σ n : ℕ, Fin n → ι), E q.swap = ∑' q, E q`. Rewrite using `[← (Equiv.prodComm (Σ n : ℕ, Fin n → ι) ℕ).tsum_eq]`. Simplify using the standard rewrite rules. Rewrite using `[← hEsum, ← ht]`. Conclude with `hEs.prod_symm.hasSum`.

Use `HasSum.prod_fiberwise (g := fun n => c n * y ^ n) hsw fun n => ?_` and prove the remaining obligations. Establish `H` using `(hsw.summable.prod_factor n).hasSum`. Establish `hterm : ∀ p, E (p, n) = ((T 1 (p, n) : ℝ) : ℂ) * ((-1) ^ n * y ^ n)`. Introduce `p`. Simplify using `only [E, T]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hval : ∑' p, E (n, p).swap = c n * y ^ n`. Simplify using `only [Prod.swap_prod_mk, hterm]`. Rewrite using `[tsum_mul_right, ← Complex.ofReal_tsum]`.

Simplify using `only [c, r]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `H` using `[hval]`. Conclude with `H`. Establish `hent` using `hF.hasFPowerSeriesOnBall 2 (R := 1) one_pos`.

Establish `hpeq` using `hps.hasFPowerSeriesAt.eq_formalMultilinearSeries hent.hasFPowerSeriesAt`. Rewrite `hent` using `[← hpeq]`. Establish `H0` using `hent.hasSum (y := -2) (EMetric.mem_ball.mpr (edist_lt_top _ _))`. Simplify using `only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at H0`. Establish `hterm : ∀ n, c n * (-2) ^ n = ((∑' p, T 2 (p, n) : ℝ) : ℂ)`.

Introduce `n`. Establish `h2 : ∀ p, T 2 (p, n) = T 1 (p, n) * 2 ^ n`. Introduce `p`. Simplify using `only [T]`. Rewrite using `[mul_pow, mul_pow, one_pow]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h2, tsum_mul_right, c, r]`. Use `push_cast`. Rewrite using `[show ((-2 : ℂ)) ^ n = (-1) ^ n * 2 ^ n by rw [← mul_pow]; norm_num]`. Put the polynomial expressions in normal form.

Rewrite using `[mul_comm n 2, pow_mul]`. Evaluate the numerical expressions. Simplify using `only [hterm] at H0`. Establish `hS2 : Summable fun n => ∑' p, T 2 (p, n)` using `Complex.summable_ofReal.mp H0.summable`. Establish `hall : Summable fun q : ℕ × (Σ n : ℕ, Fin n → ι) => T 2 q.swap` using `(summable_prod_of_nonneg (fun q => hT 2 (by norm_num) q.swap)).mpr ⟨fun n => hK 2 (by norm_num) n, hS2⟩`.

Establish `hall' : Summable (T 2)`. Use `hall.prod_symm` as an intermediate fact. Simplify using `using this`. Establish `hbsum : Summable b`. Use `((summable_prod_of_nonneg (hT 2 (by norm_num))).mp hall').2` as an intermediate fact.

Simplify using `only [fun p => (hfib 2 p).tsum_eq, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at this`. Conclude with `this`. Set `j : ι → (Σ n : ℕ, Fin n → ι)` to `fun i => ⟨1, fun _ => i⟩`. Establish `hj : Function.Injective j`. Introduce `i i' h`.

Simplify using `only [j, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h`. Conclude with `congrFun h 0`. Establish `hbj : b ∘ j = a`. Use function extensionality and compare the values at `i`. Simplify using `[b, j]`.

Rewrite using `[← hbj]`. Conclude with `hbsum.comp_injective hj`.
-/
theorem _root_.GlobalTheory.landau_exp_summable : ∀ (ι : Type) (a l : ι → ℝ) (F : ℂ → ℂ),
    (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ l i) → Differentiable ℂ F →
    (∀ s : ℂ, 1 < s.re → ∃ g : ℂ, HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * s)) g ∧
      F s = Complex.exp g) → Summable a := by
  intro ι a l F ha hl hF hD
  let b : (Σ n : ℕ, Fin n → ι) → ℝ := fun p => (∏ k, a (p.2 k)) / (p.1.factorial : ℝ)
  let L : (Σ n : ℕ, Fin n → ι) → ℝ := fun p => ∑ k, l (p.2 k)
  have hb : ∀ p, 0 ≤ b p := fun p =>
    div_nonneg (Finset.prod_nonneg fun k _ => ha _) (Nat.cast_nonneg _)
  have hL : ∀ p, 0 ≤ L p := fun p => Finset.sum_nonneg fun k _ => hl _

  have hA : ∀ s : ℂ, 1 < s.re →
      HasSum (fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * s)) (F s) := by
    intro s hs
    obtain ⟨g, hg, hFg⟩ := hD s hs
    rw [hFg]
    have H := _root_.GlobalTheory.hasSum_tuple_prod_exp _ g hg
    have heq : (fun p : (Σ n : ℕ, Fin n → ι) =>
        (∏ k, (a (p.2 k) : ℂ) * Complex.exp (-(l (p.2 k) : ℂ) * s)) / (p.1.factorial : ℂ)) =
        fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * s) := by
      funext p
      have hsum : ∑ k, (-(l (p.2 k) : ℂ) * s) = -(L p : ℂ) * s := by
        simp only [L, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_neg_distrib, neg_mul]
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hsum]
      simp only [b, Complex.ofReal_div, Complex.ofReal_prod, Complex.ofReal_natCast]
      ring
    rw [heq] at H
    exact H
  have hB : ∀ σ : ℝ, 1 < σ → Summable fun p => b p * Real.exp (-(L p * σ)) := by
    intro σ hσ
    have H := (hA σ (by simpa using hσ)).summable
    have heq : (fun p => (b p : ℂ) * Complex.exp (-(L p : ℂ) * (σ : ℂ))) =
        fun p => ((b p * Real.exp (-(L p * σ)) : ℝ) : ℂ) := by
      funext p
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      push_cast
      ring_nf
    rw [heq] at H
    exact Complex.summable_ofReal.mp H
  have hexpR : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    intro x
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hexpC : ∀ x : ℂ, HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ)) (Complex.exp x) := by
    intro x
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp x

  let T : ℝ → (Σ n : ℕ, Fin n → ι) × ℕ → ℝ := fun t q =>
    b q.1 * Real.exp (-(2 * L q.1)) * ((L q.1 * t) ^ q.2 / (q.2.factorial : ℝ))
  have hT : ∀ t, 0 ≤ t → ∀ q, 0 ≤ T t q := by
    intro t ht q
    have := hL q.1
    exact mul_nonneg (mul_nonneg (hb _) (Real.exp_pos _).le) (by positivity)
  have hfib : ∀ t p, HasSum (fun n => T t (p, n)) (b p * Real.exp (-(L p * (2 - t)))) := by
    intro t p
    have H := (hexpR (L p * t)).mul_left (b p * Real.exp (-(2 * L p)))
    rw [show -(L p * (2 - t)) = -(2 * L p) + L p * t by ring, Real.exp_add, ← mul_assoc]
    exact H
  have hK : ∀ t, 0 ≤ t → ∀ n, Summable fun p => T t (p, n) := by
    intro t ht n
    refine Summable.of_nonneg_of_le (fun p => hT t ht (p, n)) (fun p => ?_)
      ((hB (7 / 4) (by norm_num)).mul_left ((4 * t) ^ n))
    have hLp := hL p
    have h1 : (L p * t) ^ n / (n.factorial : ℝ) = (4 * t) ^ n * ((L p / 4) ^ n / n.factorial) := by
      rw [show L p * t = (4 * t) * (L p / 4) by ring, mul_pow, mul_div_assoc]
    have h2 : (L p / 4) ^ n / (n.factorial : ℝ) ≤ Real.exp (L p / 4) :=
      Real.pow_div_factorial_le_exp _ (by positivity) n
    have h3 : b p * Real.exp (-(2 * L p)) * ((4 * t) ^ n * Real.exp (L p / 4)) =
        (4 * t) ^ n * (b p * Real.exp (-(L p * (7 / 4)))) := by
      rw [show -(L p * (7 / 4)) = -(2 * L p) + L p / 4 by ring, Real.exp_add]
      ring
    change b p * Real.exp (-(2 * L p)) * ((L p * t) ^ n / (n.factorial : ℝ)) ≤ _
    rw [h1, ← h3]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) n))
      (mul_nonneg (hb p) (Real.exp_pos _).le)
  have hK2 : ∀ t, 0 ≤ t → t < 1 → Summable (T t) := by
    intro t ht ht1
    rw [summable_prod_of_nonneg (fun q => hT t ht q)]
    refine ⟨fun p => (hfib t p).summable, ?_⟩
    simp only [fun p => (hfib t p).tsum_eq]
    exact hB (2 - t) (by linarith)
  have hK2' : ∀ t, 0 ≤ t → t < 1 →
      Summable fun n => ∑' p, T t (p, n) := by
    intro t ht ht1
    have hs : Summable fun q : ℕ × (Σ n : ℕ, Fin n → ι) => T t q.swap :=
      (hK2 t ht ht1).prod_symm
    exact ((summable_prod_of_nonneg (fun q => hT t ht q.swap)).mp hs).2

  let r : ℕ → ℝ := fun n => ∑' p, T 1 (p, n)
  let c : ℕ → ℂ := fun n => (-1) ^ n * (r n : ℂ)
  have hr : ∀ n, 0 ≤ r n := fun n => tsum_nonneg fun p => hT 1 zero_le_one (p, n)
  have hrad : 1 ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ => ?_
    have hρ1 : (ρ : ℝ) < 1 := by exact_mod_cast hρ
    have hρ0 : (0 : ℝ) ≤ ρ := ρ.2
    refine FormalMultilinearSeries.le_radius_of_bound _
      (∑' m, ∑' p, T ρ (p, m)) fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm_eq_mul,
      ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
    have hcn : ‖c n‖ = r n := by
      simp only [c, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr n)]
    have hrn : r n * (ρ : ℝ) ^ n = ∑' p, T ρ (p, n) := by
      simp only [r, ← tsum_mul_right]
      congr 1
      funext p
      simp only [T]
      rw [mul_pow, mul_pow, one_pow]
      ring
    rw [hcn, hrn]
    exact (hK2' ρ hρ0 hρ1).le_tsum n fun m _ => tsum_nonneg fun p => hT ρ hρ0 (p, m)
  have hps : HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℂ c) 2 1 := by
    refine ⟨hrad, one_pos, fun {y} hy => ?_⟩
    have hy1 : ‖y‖ < 1 := by
      simpa [EMetric.mem_ball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one] using hy
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    let E : (Σ n : ℕ, Fin n → ι) × ℕ → ℂ := fun q =>
      ((b q.1 * Real.exp (-(2 * L q.1)) : ℝ) : ℂ) * ((-(L q.1 : ℂ) * y) ^ q.2 / (q.2.factorial : ℂ))
    have hEn : ∀ q, ‖E q‖ = T ‖y‖ q := by
      intro q
      simp only [E, T, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real,
        Complex.norm_natCast, Real.norm_eq_abs]
      rw [abs_of_nonneg (hb q.1), Real.abs_exp, abs_of_nonneg (hL q.1)]
    have hEs : Summable E := by
      refine Summable.of_norm ?_
      simp only [hEn]
      exact hK2 ‖y‖ (norm_nonneg _) hy1
    have hfibE : ∀ p, HasSum (fun n => E (p, n))
        ((b p : ℂ) * Complex.exp (-(L p : ℂ) * (2 + y))) := by
      intro p
      have H := (hexpC (-(L p : ℂ) * y)).mul_left ((b p * Real.exp (-(2 * L p)) : ℝ) : ℂ)
      have heq : ((b p * Real.exp (-(2 * L p)) : ℝ) : ℂ) * Complex.exp (-(L p : ℂ) * y) =
          (b p : ℂ) * Complex.exp (-(L p : ℂ) * (2 + y)) := by
        rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
        push_cast
        ring_nf
      rw [heq] at H
      exact H
    have hre : 1 < (2 + y).re := by
      have := Complex.abs_re_le_norm y
      rw [Complex.add_re]
      norm_num
      linarith [abs_le.mp this]
    have hEsum : ∑' q, E q = F (2 + y) :=
      (hEs.hasSum.prod_fiberwise hfibE).unique (hA _ hre)
    have hsw : HasSum (fun q : ℕ × (Σ n : ℕ, Fin n → ι) => E q.swap) (F (2 + y)) := by
      have ht : ∑' q : ℕ × (Σ n : ℕ, Fin n → ι), E q.swap = ∑' q, E q := by
        rw [← (Equiv.prodComm (Σ n : ℕ, Fin n → ι) ℕ).tsum_eq]
        simp
      rw [← hEsum, ← ht]
      exact hEs.prod_symm.hasSum
    refine HasSum.prod_fiberwise (g := fun n => c n * y ^ n) hsw fun n => ?_
    have H := (hsw.summable.prod_factor n).hasSum
    have hterm : ∀ p, E (p, n) = ((T 1 (p, n) : ℝ) : ℂ) * ((-1) ^ n * y ^ n) := by
      intro p
      simp only [E, T]
      push_cast
      ring
    have hval : ∑' p, E (n, p).swap = c n * y ^ n := by
      simp only [Prod.swap_prod_mk, hterm]
      rw [tsum_mul_right, ← Complex.ofReal_tsum]
      simp only [c, r]
      ring
    rw [hval] at H
    exact H

  have hent := hF.hasFPowerSeriesOnBall 2 (R := 1) one_pos
  have hpeq := hps.hasFPowerSeriesAt.eq_formalMultilinearSeries hent.hasFPowerSeriesAt
  rw [← hpeq] at hent
  have H0 := hent.hasSum (y := -2) (EMetric.mem_ball.mpr (edist_lt_top _ _))
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at H0
  have hterm : ∀ n, c n * (-2) ^ n = ((∑' p, T 2 (p, n) : ℝ) : ℂ) := by
    intro n
    have h2 : ∀ p, T 2 (p, n) = T 1 (p, n) * 2 ^ n := by
      intro p
      simp only [T]
      rw [mul_pow, mul_pow, one_pow]
      ring
    simp only [h2, tsum_mul_right, c, r]
    push_cast
    rw [show ((-2 : ℂ)) ^ n = (-1) ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
    ring_nf
    rw [mul_comm n 2, pow_mul]
    norm_num
  simp only [hterm] at H0
  have hS2 : Summable fun n => ∑' p, T 2 (p, n) := Complex.summable_ofReal.mp H0.summable
  have hall : Summable fun q : ℕ × (Σ n : ℕ, Fin n → ι) => T 2 q.swap :=
    (summable_prod_of_nonneg (fun q => hT 2 (by norm_num) q.swap)).mpr
      ⟨fun n => hK 2 (by norm_num) n, hS2⟩
  have hall' : Summable (T 2) := by
    have := hall.prod_symm
    simpa using this
  have hbsum : Summable b := by
    have := ((summable_prod_of_nonneg (hT 2 (by norm_num))).mp hall').2
    simp only [fun p => (hfib 2 p).tsum_eq, sub_self, mul_zero, neg_zero, Real.exp_zero,
      mul_one] at this
    exact this

  let j : ι → (Σ n : ℕ, Fin n → ι) := fun i => ⟨1, fun _ => i⟩
  have hj : Function.Injective j := by
    intro i i' h
    simp only [j, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact congrFun h 0
  have hbj : b ∘ j = a := by
    funext i
    simp [b, j]
  rw [← hbj]
  exact hbsum.comp_injective hj

end GlobalTheory
