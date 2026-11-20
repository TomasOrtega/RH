import ReciprocityTheory.SemistableReduction.TorusLexB

namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

open MeasureTheory ComplexConjugate

/- English proof (translation)
Unfold `torusMono`. Rewrite using `[norm_prod]`. Simplify using `[norm_pow, norm_torusPoint]`.
-/
private theorem norm_torusMono_eq_one {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  unfold torusMono
  rw [norm_prod]
  simp [norm_pow, norm_torusPoint]

/- English proof (translation)
Establish `h : ∀ i, Continuous fun θ : ι → ℝ => torusPoint θ i` using `fun i => (continuous_apply i).comp continuous_torusPoint`. Unfold `torusMono`. Conclude with `continuous_finset_prod _ (fun i _ => (h i).pow _)`.
-/
private theorem continuous_torusMono' {ι : Type} [Fintype ι] (s : ι →₀ ℕ) :
    Continuous (fun θ : ι → ℝ => torusMono θ s) := by
  have h : ∀ i, Continuous fun θ : ι → ℝ => torusPoint θ i :=
    fun i => (continuous_apply i).comp continuous_torusPoint
  unfold torusMono
  exact continuous_finset_prod _ (fun i _ => (h i).pow _)

/- English proof (translation)
Use `integrable_of_bdd ((continuous_eval_torus f).mul (Complex.continuous_conj.comp (continuous_torusMono' s))) (∑ t ∈ f.support, ‖f.coeff t‖) (fun θ => ?_)` and prove the remaining obligations. Establish `h` using `norm_eval_torus_le f θ`. Simplify `h` using `[norm_torusMono_eq_one]`.
-/
theorem integrable_torus_term {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    Integrable (fun θ => MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s))
      (torusProb ι) := by
  refine integrable_of_bdd ((continuous_eval_torus f).mul
    (Complex.continuous_conj.comp (continuous_torusMono' s))) (∑ t ∈ f.support, ‖f.coeff t‖)
    (fun θ => ?_)
  have h := norm_eval_torus_le f θ
  simpa [norm_torusMono_eq_one] using h

/- English proof (translation)
Use `integrable_of_bdd ((continuous_torusMono' t).mul (Complex.continuous_conj.comp (continuous_torusMono' s))) 1 (fun θ => ?_)` and prove the remaining obligations. Simplify using `[norm_torusMono_eq_one]`.
-/
theorem integrable_mono_term {ι : Type} [Fintype ι] (t s : ι →₀ ℕ) :
    Integrable (fun θ => torusMono θ t * conj (torusMono θ s)) (torusProb ι) := by
  refine integrable_of_bdd ((continuous_torusMono' t).mul
    (Complex.continuous_conj.comp (continuous_torusMono' s))) 1 (fun θ => ?_)
  simp [norm_torusMono_eq_one]

/- English proof (translation)
Repeatedly rewrite using `[eval_torus, Finset.sum_mul]`. Rewrite using `[integral_finset_sum _ (fun t _ => by`. Simplify `(integrable_mono_term t s).const_mul (f.coeff t))]` using `[mul_assoc]`. Repeatedly rewrite using `[mul_assoc, integral_const_mul, torus_orth, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq']`.

Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `(MvPolynomial.notMem_support_iff.mp h).symm`.
-/
theorem torus_coeff_integral {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∫ θ, MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s) ∂(torusProb ι) =
      f.coeff s := by
  simp_rw [eval_torus, Finset.sum_mul]
  rw [integral_finset_sum _ (fun t _ => by
    simpa [mul_assoc] using (integrable_mono_term t s).const_mul (f.coeff t))]
  simp_rw [mul_assoc, integral_const_mul, torus_orth, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (MvPolynomial.notMem_support_iff.mp h).symm

/- English proof (translation)
Establish `key : ∀ θ, ((‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 : ℝ) : ℂ) = ∑ s ∈ f.support, conj (f.coeff s) * (MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s))`. Introduce `θ`. Establish `hc : conj (MvPolynomial.eval (torusPoint θ) f) = ∑ s ∈ f.support, conj (f.coeff s) * conj (torusMono θ s)` using `by conv_lhs => rw [eval_torus]`. Simplify using `[map_sum, map_mul]`. Use `push_cast`.

Rewrite using `[show ((‖MvPolynomial.eval (torusPoint θ) f‖ : ℂ)) ^ 2 = MvPolynomial.eval (torusPoint θ) f * conj (MvPolynomial.eval (torusPoint θ) f) by`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Use the proof step `ring]`. Rewrite using `[hc, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← integral_complex_ofReal]`. Repeatedly rewrite using `[key]`.

Rewrite using `[integral_finset_sum _ (fun s _ => (integrable_torus_term f s).const_mul _)]`. Repeatedly rewrite using `[integral_const_mul, torus_coeff_integral]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem torus_parseval {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    ∫ θ, ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 ∂(torusProb ι) =
      ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 := by
  have key : ∀ θ, ((‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 : ℝ) : ℂ) =
      ∑ s ∈ f.support, conj (f.coeff s) *
        (MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)) := by
    intro θ
    have hc : conj (MvPolynomial.eval (torusPoint θ) f) =
        ∑ s ∈ f.support, conj (f.coeff s) * conj (torusMono θ s) := by
      conv_lhs => rw [eval_torus]
      simp [map_sum, map_mul]
    push_cast
    rw [show ((‖MvPolynomial.eval (torusPoint θ) f‖ : ℂ)) ^ 2 =
        MvPolynomial.eval (torusPoint θ) f * conj (MvPolynomial.eval (torusPoint θ) f) by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  rw [integral_finset_sum _ (fun s _ => (integrable_torus_term f s).const_mul _)]
  simp_rw [integral_const_mul, torus_coeff_integral]
  push_cast
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [torusPoint]`. Rewrite using `[← Int.self_sub_floor]`. Use `push_cast`. Rewrite using `[mul_sub, Complex.exp_sub]`.

Establish `h : Complex.exp (2 * Real.pi * Complex.I * ((⌊θ i⌋ : ℤ) : ℂ)) = 1`. Rewrite using `[show 2 * Real.pi * Complex.I * ((⌊θ i⌋ : ℤ) : ℂ) = (⌊θ i⌋ : ℤ) * (2 * Real.pi * Complex.I) by ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I _`. Rewrite using `[h, div_one]`.
-/
theorem torusPoint_fract {ι : Type} (θ : ι → ℝ) :
    torusPoint (fun i => Int.fract (θ i)) = torusPoint θ := by
  funext i
  simp only [torusPoint]
  rw [← Int.self_sub_floor]
  push_cast
  rw [mul_sub, Complex.exp_sub]
  have h : Complex.exp (2 * Real.pi * Complex.I * ((⌊θ i⌋ : ℤ) : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * ((⌊θ i⌋ : ℤ) : ℂ) = (⌊θ i⌋ : ℤ) * (2 * Real.pi * Complex.I) by
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h, div_one]

/- English proof (translation)
Take `⟨θ₀, -, hθ₀⟩` from `(isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_isMaxOn ⟨fun _ => 0, fun i _ => by simp⟩ (continuous_eval_torus f).norm.continuousOn`. Use `⟨θ₀, fun θ => ?_⟩` and prove the remaining obligations. Establish `hmem : (fun i => Int.fract (θ i)) ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)` using `fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩`. Establish `h` using `isMaxOn_iff.mp hθ₀ _ hmem`. Simplify using `only [torusPoint_fract] at h`.

Conclude with `h`.
-/
theorem exists_torus_max {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    ∃ θ₀ : ι → ℝ, ∀ θ, ‖MvPolynomial.eval (torusPoint θ) f‖ ≤
      ‖MvPolynomial.eval (torusPoint θ₀) f‖ := by
  obtain ⟨θ₀, -, hθ₀⟩ := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_isMaxOn
    ⟨fun _ => 0, fun i _ => by simp⟩ (continuous_eval_torus f).norm.continuousOn
  refine ⟨θ₀, fun θ => ?_⟩
  have hmem : (fun i => Int.fract (θ i)) ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have h := isMaxOn_iff.mp hθ₀ _ hmem
  simp only [torusPoint_fract] at h
  exact h

/- English proof (translation)
Introduce `ι _ f`. Use `haveI := torusProb_isProb ι`. Take `⟨hInt, hMul, hMono⟩` from `hBasic ι`. Prove the components needed by the constructor for the conclusion. Introduce `hf set A := ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 with hA`.

Establish `hApos : 0 < A`. Take `⟨s, hs⟩` from `Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hf)`. Conclude with `Finset.sum_pos' (fun _ _ => by positivity) ⟨s, hs, pow_pos (norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hs)) 2⟩`. Establish `hq : 0 < Real.exp 1 / A` using `div_pos (Real.exp_pos 1) hApos`. Use `set r : ℝ := Real.sqrt (Real.exp 1 / A) with hrdef`.

Establish `hr : 0 < r` using `Real.sqrt_pos.mpr hq`. Establish `hr2 : r ^ 2 = Real.exp 1 / A` using `Real.sq_sqrt hq.le`. Establish `hc : ((r : ℂ)) ≠ 0` using `by exact_mod_cast hr.ne'`. Establish `hcn : ‖(r : ℂ)‖ = r` using `by simp [abs_of_pos hr]`. Establish `hCc : (MvPolynomial.C (r : ℂ) : MvPolynomial ι ℂ) ≠ 0` using `by simpa using hc`.

Establish `hmean : torusMean (MvPolynomial.C (r : ℂ) * f) = Real.log r + torusMean f`. Rewrite using `[hMul _ _ hCc hf, MvPolynomial.C_apply, hMono, hcn]`. Establish `hpt : ∀ θ, Real.log ‖MvPolynomial.eval (torusPoint θ) (MvPolynomial.C (r : ℂ) * f)‖ ≤ r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2`. Introduce `θ`. Rewrite using `[MvPolynomial.eval_mul, MvPolynomial.eval_C, norm_mul, hcn]`.

Establish `hx : 0 ≤ ‖MvPolynomial.eval (torusPoint θ) f‖` using `norm_nonneg _`. Break down `hx.eq_or_lt with h0 | hpos` into its components or cases. Rewrite using `[← h0]`. Simplify using the standard rewrite rules. Establish `hy : 0 < (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1` using `by positivity`.

Establish `h1` using `Real.log_le_sub_one_of_pos hy`. Rewrite `h1` using `[Real.log_div (ne_of_gt (by positivity)) (Real.exp_pos 1).ne', Real.log_exp, Real.log_pow]`. Establish `e2 : (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 = r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2` using `by ring`. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hint2 : Integrable (fun θ => ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2) (torusProb ι)` using `integrable_of_bdd ((continuous_eval_torus f).norm.pow 2) ((∑ s ∈ f.support, ‖f.coeff s‖) ^ 2) (fun θ => by`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (norm_eval_torus_le f θ) 2)`. Establish `hle : torusMean (MvPolynomial.C (r : ℂ) * f) ≤ r ^ 2 / Real.exp 1 * A / 2`. Unfold `torusMean`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_div, integral_const_mul, torus_parseval]`. Establish `h12 : r ^ 2 / Real.exp 1 * A / 2 = 1 / 2`. Rewrite using `[hr2]`. Clear the denominators using the available nonvanishing facts.

Establish `hlogr : Real.log r = (1 - Real.log A) / 2`. Rewrite using `[hrdef, Real.log_sqrt hq.le, Real.log_div (Real.exp_pos 1).ne' hApos.ne', Real.log_exp]`. Unfold `polyL2`. Rewrite using `[← hA, Real.log_sqrt hApos.le]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `s`. Take `⟨θ₀, hθ₀⟩` from `exists_torus_max f`. Use `⟨θ₀, ?_⟩` and prove the remaining obligations. Rewrite using `[← torus_coeff_integral f s]`. Establish `hb : ∀ᵐ θ ∂(torusProb ι), ‖MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)‖ ≤ ‖MvPolynomial.eval (torusPoint θ₀) f‖` using `Filter.Eventually.of_forall (fun θ => by simpa [norm_torusMono_eq_one] using hθ₀ θ)`.

Simplify using `using norm_integral_le_of_norm_le_const hb`.
-/
theorem torus_l2_cauchy_of_basic (hBasic : TorusMeanBasicStatement) : TorusL2Cauchy := by
  intro ι _ f
  haveI := torusProb_isProb ι
  obtain ⟨hInt, hMul, hMono⟩ := hBasic ι
  constructor
  · intro hf
    set A := ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 with hA
    have hApos : 0 < A := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hf)
      exact Finset.sum_pos' (fun _ _ => by positivity)
        ⟨s, hs, pow_pos (norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hs)) 2⟩
    have hq : 0 < Real.exp 1 / A := div_pos (Real.exp_pos 1) hApos
    set r : ℝ := Real.sqrt (Real.exp 1 / A) with hrdef
    have hr : 0 < r := Real.sqrt_pos.mpr hq
    have hr2 : r ^ 2 = Real.exp 1 / A := Real.sq_sqrt hq.le
    have hc : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
    have hcn : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
    have hCc : (MvPolynomial.C (r : ℂ) : MvPolynomial ι ℂ) ≠ 0 := by simpa using hc
    have hmean : torusMean (MvPolynomial.C (r : ℂ) * f) = Real.log r + torusMean f := by
      rw [hMul _ _ hCc hf, MvPolynomial.C_apply, hMono, hcn]
    have hpt : ∀ θ, Real.log ‖MvPolynomial.eval (torusPoint θ) (MvPolynomial.C (r : ℂ) * f)‖ ≤
        r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2 := by
      intro θ
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, norm_mul, hcn]
      have hx : 0 ≤ ‖MvPolynomial.eval (torusPoint θ) f‖ := norm_nonneg _
      rcases hx.eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hy : 0 < (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 := by positivity
        have h1 := Real.log_le_sub_one_of_pos hy
        rw [Real.log_div (ne_of_gt (by positivity)) (Real.exp_pos 1).ne', Real.log_exp,
          Real.log_pow] at h1
        have e2 : (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 =
            r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 := by ring
        push_cast at h1
        linarith
    have hint2 : Integrable (fun θ => ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2) (torusProb ι) :=
      integrable_of_bdd ((continuous_eval_torus f).norm.pow 2) ((∑ s ∈ f.support, ‖f.coeff s‖) ^ 2)
        (fun θ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_eval_torus_le f θ) 2)
    have hle : torusMean (MvPolynomial.C (r : ℂ) * f) ≤ r ^ 2 / Real.exp 1 * A / 2 := by
      unfold torusMean
      calc _ ≤ ∫ θ, r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2 ∂(torusProb ι) :=
            integral_mono (hInt _ (mul_ne_zero hCc hf)) ((hint2.const_mul _).div_const 2) hpt
        _ = r ^ 2 / Real.exp 1 * A / 2 := by
            rw [integral_div, integral_const_mul, torus_parseval]
    have h12 : r ^ 2 / Real.exp 1 * A / 2 = 1 / 2 := by
      rw [hr2]; field_simp
    have hlogr : Real.log r = (1 - Real.log A) / 2 := by
      rw [hrdef, Real.log_sqrt hq.le, Real.log_div (Real.exp_pos 1).ne' hApos.ne', Real.log_exp]
    unfold polyL2
    rw [← hA, Real.log_sqrt hApos.le]
    linarith
  · intro s
    obtain ⟨θ₀, hθ₀⟩ := exists_torus_max f
    refine ⟨θ₀, ?_⟩
    rw [← torus_coeff_integral f s]
    have hb : ∀ᵐ θ ∂(torusProb ι), ‖MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)‖ ≤
        ‖MvPolynomial.eval (torusPoint θ₀) f‖ :=
      Filter.Eventually.of_forall (fun θ => by simpa [norm_torusMono_eq_one] using hθ₀ θ)
    simpa using norm_integral_le_of_norm_le_const hb

end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
