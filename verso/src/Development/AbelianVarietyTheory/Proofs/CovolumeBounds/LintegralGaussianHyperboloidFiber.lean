import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LintegralHyperboloidFibrationStatement
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.ConeSlice

noncomputable abbrev sgnMat (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1)

noncomputable abbrev pt {k : ℕ} (τ : ℝ) (p : (Fin k → ℂ) × ℝ) : Fin (k + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))

/- English proof (translation)
Unfold `sqLen`. Conclude with `continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)`.
-/
theorem continuous_sqLen {n : ℕ} : Continuous (sqLen : (Fin n → ℂ) → ℝ) := by
  unfold sqLen
  exact continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

/- English proof (translation)
Simplify using `only [dotProduct, sgnMat, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, sqLen, Fin.init, Pi.star_apply, Fin.castSucc_ne_last, if_false, if_true, one_mul]`. Use `push_cast`. Simplify using `only [Complex.normSq_eq_conj_mul_self, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_eq {k : ℕ} (v : Fin (k + 1) → ℂ) :
    star v ⬝ᵥ (sgnMat k *ᵥ v) =
      ((sqLen (Fin.init v : Fin k → ℂ) - Complex.normSq (v (Fin.last k)) : ℝ) : ℂ) := by
  simp only [dotProduct, sgnMat, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, sqLen, Fin.init,
    Pi.star_apply, Fin.castSucc_ne_last, if_false, if_true, one_mul]
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/- English proof (translation)
Establish `h : star (g *ᵥ v) ⬝ᵥ (sgnMat k *ᵥ (g *ᵥ v)) = star v ⬝ᵥ (sgnMat k *ᵥ v)` using `by conv_rhs => rw [← hg]`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Rewrite `h` using `[form_eq, form_eq, Complex.ofReal_inj]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem form_inv {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) (v : Fin (k + 1) → ℂ) :
    Complex.normSq ((g *ᵥ v) (Fin.last k)) - sqLen (Fin.init (g *ᵥ v) : Fin k → ℂ) =
      Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ) := by
  have h : star (g *ᵥ v) ⬝ᵥ (sgnMat k *ᵥ (g *ᵥ v)) = star v ⬝ᵥ (sgnMat k *ᵥ v) := by
    conv_rhs => rw [← hg]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [form_eq, form_eq, Complex.ofReal_inj] at h
  linarith

/- English proof (translation)
Establish `h` using `congrArg Matrix.det hg`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `hD : (sgnMat k).det ≠ 0`. Rewrite using `[Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h2 : (Complex.normSq g.det : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Apply `mul_left_cancel₀ hD` to reduce the goal to its premises. Rewrite using `[mul_one]`.

Rewrite `h` using `[Complex.star_def]`. Take the linear combination `h`. Conclude with `h2` after adjusting the coercions.
-/
theorem normSq_det {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) : Complex.normSq g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hD : (sgnMat k).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs <;> simp
  have h2 : (Complex.normSq g.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    apply mul_left_cancel₀ hD
    rw [mul_one]
    rw [Complex.star_def] at h
    linear_combination h
  exact_mod_cast h2

/- English proof (translation)
The claim follows from `(Matrix.toLin' g).continuous_of_finiteDimensional`.
-/
theorem continuous_mulVec {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun v : Fin n → ℂ => g *ᵥ v) :=
  (Matrix.toLin' g).continuous_of_finiteDimensional

/- English proof (translation)
Establish `hdet : LinearMap.det ((Matrix.toLin' g).restrictScalars ℝ) = 1`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hg]`. Use `⟨(continuous_mulVec g).measurable, ?_⟩` and prove the remaining obligations. Establish `h` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ)) (f := (Matrix.toLin' g).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)`. Rewrite `h` using `[hdet]`.

Simplify using `only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h`. Conclude with `h`.
-/
theorem measurePreserving_mulVec {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Complex.normSq g.det = 1) :
    MeasurePreserving (fun v : Fin n → ℂ => g *ᵥ v) volume volume := by
  have hdet : LinearMap.det ((Matrix.toLin' g).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hg]
  refine ⟨(continuous_mulVec g).measurable, ?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ))
    (f := (Matrix.toLin' g).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

/- English proof (translation)
Use `set L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' g⁻¹)`. Use `⟨((n * ‖L‖ ^ 2) + 1)⁻¹, by positivity, fun v => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ u : Fin n → ℂ, 0 ≤ sqLen u` using `fun u => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _`. Establish `h1 : ∀ u : Fin n → ℂ, sqLen u ≤ n * ‖u‖ ^ 2` using `fun u => by`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Complex.normSq_eq_norm_sq]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 2`. Use `_ = _ := by simp`. Establish `h2 : ∀ u : Fin n → ℂ, ‖u‖ ^ 2 ≤ sqLen u` using `fun u => by`. Establish `: ‖u‖ ≤ Real.sqrt (sqLen u)`.

Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Rewrite using `[← Complex.normSq_eq_norm_sq]`. Conclude with `Finset.single_le_sum (f := fun i => Complex.normSq (u i)) (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3 : L (g *ᵥ v) = v`. Simplify using `[L, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g (Ne.isUnit hg)]`. Establish `h4 : ‖v‖ ≤ ‖L‖ * ‖g *ᵥ v‖` using `by conv_lhs => rw [← h3]`. Conclude with `L.le_opNorm _`. Establish `h5 : ‖v‖ ^ 2 ≤ ‖L‖ ^ 2 * sqLen (g *ᵥ v)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_le_iff₀ (by positivity)]`. Establish `h6` using `mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (α := ℝ) n)`. Use `h1 v` as an intermediate fact. Use `h0 (g *ᵥ v)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_lower {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g.det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * sqLen v ≤ sqLen (g *ᵥ v) := by
  set L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' g⁻¹)
  refine ⟨((n * ‖L‖ ^ 2) + 1)⁻¹, by positivity, fun v => ?_⟩
  have h0 : ∀ u : Fin n → ℂ, 0 ≤ sqLen u := fun u =>
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h1 : ∀ u : Fin n → ℂ, sqLen u ≤ n * ‖u‖ ^ 2 := fun u => by
    calc sqLen u ≤ ∑ _i : Fin n, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [Complex.normSq_eq_norm_sq]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 2
      _ = _ := by simp
  have h2 : ∀ u : Fin n → ℂ, ‖u‖ ^ 2 ≤ sqLen u := fun u => by
    have : ‖u‖ ≤ Real.sqrt (sqLen u) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      apply Real.le_sqrt_of_sq_le
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (f := fun i => Complex.normSq (u i))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    calc ‖u‖ ^ 2 ≤ Real.sqrt (sqLen u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt (h0 u)
  have h3 : L (g *ᵥ v) = v := by
    simp [L, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g (Ne.isUnit hg)]
  have h4 : ‖v‖ ≤ ‖L‖ * ‖g *ᵥ v‖ := by
    conv_lhs => rw [← h3]
    exact L.le_opNorm _
  have h5 : ‖v‖ ^ 2 ≤ ‖L‖ ^ 2 * sqLen (g *ᵥ v) := by
    calc ‖v‖ ^ 2 ≤ (‖L‖ * ‖g *ᵥ v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
      _ = ‖L‖ ^ 2 * ‖g *ᵥ v‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h2 _) (by positivity)
  rw [inv_mul_le_iff₀ (by positivity)]
  have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (α := ℝ) n)
  have := h1 v
  have := h0 (g *ᵥ v)
  nlinarith

/- English proof (translation)
Establish `h1 : Integrable (fun z : ℂ => Real.exp (-(c * Complex.normSq z)))`. Establish `h` using `(GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ)) (by simpa using hc) 0 0).norm`. Use `h.congr (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [Complex.norm_exp, Complex.normSq_eq_norm_sq]`. Use `congr 1`.

Simplify using `[← Complex.ofReal_pow]`. Establish `h2` using `Integrable.fintype_prod (ι := Fin k) (f := fun _ (z : ℂ) => Real.exp (-(c * Complex.normSq z))) (μ := fun _ => volume) (fun _ => h1)`. Use `h2.congr (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [sqLen, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]`.
-/
theorem integrable_gauss {k : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun w : Fin k → ℂ => Real.exp (-(c * sqLen w))) := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-(c * Complex.normSq z))) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ))
      (by simpa using hc) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.norm_exp, Complex.normSq_eq_norm_sq]
    congr 1
    simp [← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin k) (f := fun _ (z : ℂ) => Real.exp (-(c * Complex.normSq z)))
    (μ := fun _ => volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [sqLen, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]

/- English proof (translation)
Use `Continuous.finSnoc (by fun_prop) ?_` and prove the remaining obligations. Use `@continuous_sqLen k` as an intermediate fact. Use `fun_prop`.
-/
theorem continuous_pt {k : ℕ} :
    Continuous (fun q : ℝ × ((Fin k → ℂ) × ℝ) => pt q.1 q.2) := by
  refine Continuous.finSnoc (by fun_prop) ?_
  have := @continuous_sqLen k
  fun_prop

/- English proof (translation)
Unfold `sqLen`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc]`. Combine the linear relations using `[Complex.normSq_nonneg (pt τ p (Fin.last k))]`.
-/
theorem sqLen_le_pt {k : ℕ} (τ : ℝ) (p : (Fin k → ℂ) × ℝ) : sqLen p.1 ≤ sqLen (pt τ p) := by
  unfold sqLen
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc]
  linarith [Complex.normSq_nonneg (pt τ p (Fin.last k))]

noncomputable def slice {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi),
    ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ pt τ p)))

/- English proof (translation)
Take `⟨c, hc, hle⟩` from `exists_lower hg`. Establish `hcont : Continuous (fun q : ℝ × ((Fin k → ℂ) × ℝ) => ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ pt q.1 q.2))))` using `ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_sqLen.comp ((continuous_mulVec g).comp continuous_pt)).neg)`. Establish `hint : Integrable (fun p : (Fin k → ℂ) × ℝ => Real.exp (-(c * sqLen p.1))) (volume.restrict (Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi)))`. Rewrite using `[Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]`. Conclude with `(integrable_gauss hc).comp_fst _`.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `τ`. Use `tendsto_lintegral_filter_of_dominated_convergence (fun p : (Fin k → ℂ) × ℝ => ENNReal.ofReal (Real.exp (-(c * sqLen p.1)))) (Filter.Eventually.of_forall fun t => (hcont.comp (Continuous.prodMk_right t)).measurable) (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall …` and prove the remaining obligations. Use `ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))` and prove the remaining obligations. Conclude with `(mul_le_mul_of_nonneg_left (sqLen_le_pt t p) hc.le).trans (hle _)`.
-/
theorem continuous_slice {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hg : g.det ≠ 0) :
    Continuous (slice g) := by
  obtain ⟨c, hc, hle⟩ := exists_lower hg
  have hcont : Continuous (fun q : ℝ × ((Fin k → ℂ) × ℝ) =>
      ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ pt q.1 q.2)))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_sqLen.comp ((continuous_mulVec g).comp continuous_pt)).neg)
  have hint : Integrable (fun p : (Fin k → ℂ) × ℝ => Real.exp (-(c * sqLen p.1)))
      (volume.restrict (Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    exact (integrable_gauss hc).comp_fst _
  rw [continuous_iff_continuousAt]
  intro τ
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun p : (Fin k → ℂ) × ℝ => ENNReal.ofReal (Real.exp (-(c * sqLen p.1))))
    (Filter.Eventually.of_forall fun t => (hcont.comp (Continuous.prodMk_right t)).measurable)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun p => ?_)
    hint.lintegral_lt_top.ne
    (Filter.Eventually.of_forall fun p => (hcont.comp (Continuous.prodMk_left p)).continuousAt)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact (mul_le_mul_of_nonneg_left (sqLen_le_pt t p) hc.le).trans (hle _)

/- English proof (translation)
Establish `hψ : Continuous (fun v : Fin (k + 1) → ℂ => ENNReal.ofReal (Real.exp (-sqLen v)))` using `ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp continuous_sqLen.neg)`. Establish `hQ : Continuous (fun v : Fin (k + 1) → ℂ => Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ))` using `(Complex.continuous_normSq.comp (continuous_apply _)).sub (continuous_sqLen.comp (continuous_pi fun i => continuous_apply _))`. Establish `h1` using `GlobalTheory.T.lintegral_hyperboloid_fibration k _ F (hψ.comp (continuous_mulVec g)).measurable hF`. Establish `h2` using `GlobalTheory.T.lintegral_hyperboloid_fibration k _ F hψ.measurable hF`. Establish `hset : {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))} = {v | 0 < Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)}`.

Use extensionality with `v`. Simplify using the standard rewrite rules. Establish `hS : MeasurableSet {v : Fin (k + 1) → ℂ | 0 < Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)}` using `(isOpen_lt continuous_const hQ).measurableSet`. Establish `h3` using `(measurePreserving_mulVec (normSq_det hg)).setLIntegral_comp_preimage hS (f := fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ENNReal.ofReal (Real.exp (-sqLen v))) ((hF.comp hQ.measurable).mul hψ.measurable)`. Simplify using `only [Set.preimage_setOf_eq, form_inv hg] at h3`.

Rewrite `h1`, `h2` using `[hset]`. Simplify using `only [Function.comp_apply] at h1`. Rewrite `h1` using `[h3, h2]`. Establish `h4` using `(ENNReal.mul_right_inj (by simp) (by simp)).1 h1`. Simplify using `only [slice, Matrix.one_mulVec]`.

Conclude with `h4.symm`.
-/
theorem lintegral_slice {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ τ in Set.Ioi 0, F τ * slice g τ = ∫⁻ τ in Set.Ioi 0, F τ * slice (k := k) 1 τ := by
  have hψ : Continuous (fun v : Fin (k + 1) → ℂ => ENNReal.ofReal (Real.exp (-sqLen v))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp continuous_sqLen.neg)
  have hQ : Continuous (fun v : Fin (k + 1) → ℂ =>
      Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) :=
    (Complex.continuous_normSq.comp (continuous_apply _)).sub
      (continuous_sqLen.comp (continuous_pi fun i => continuous_apply _))
  have h1 := GlobalTheory.T.lintegral_hyperboloid_fibration k _ F (hψ.comp (continuous_mulVec g)).measurable hF
  have h2 := GlobalTheory.T.lintegral_hyperboloid_fibration k _ F hψ.measurable hF
  have hset : {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}
      = {v | 0 < Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)} := by
    ext v; simp
  have hS : MeasurableSet {v : Fin (k + 1) → ℂ |
      0 < Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)} :=
    (isOpen_lt continuous_const hQ).measurableSet
  have h3 := (measurePreserving_mulVec (normSq_det hg)).setLIntegral_comp_preimage hS
    (f := fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) *
      ENNReal.ofReal (Real.exp (-sqLen v))) ((hF.comp hQ.measurable).mul hψ.measurable)
  simp only [Set.preimage_setOf_eq, form_inv hg] at h3
  rw [hset] at h1 h2
  simp only [Function.comp_apply] at h1
  rw [h3, h2] at h1
  have h4 := (ENNReal.mul_right_inj (by simp) (by simp)).1 h1
  simp only [slice, Matrix.one_mulVec]
  exact h4.symm

/- English proof (translation)
Establish `hd : g.det ≠ 0` using `fun h => by simpa [h] using normSq_det hg`. Establish `c1` using `continuous_slice hd`. Establish `c2` using `continuous_slice (k := k) (g := 1) (by simp)`. Establish `hae : slice g =ᵐ[volume.restrict (Set.Ioi 0)] slice (k` using `k) 1 := by`. Use `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite c1.measurable c2.measurable fun s hs _ => ?_` and prove the remaining obligations.

Establish `h` using `lintegral_slice hg (s.indicator 1) (measurable_one.indicator hs)`. Rewrite using `[← lintegral_indicator hs, ← lintegral_indicator hs]`. Apply the tactic sequence `convert h using 2 <;> ext t <;> by_cases ht : t ∈ s <;> simp [ht]`. Establish `h` using `(Measure.eqOn_open_of_ae_eq hae isOpen_Ioi c1.continuousOn c2.continuousOn).closure c1 c2`. Rewrite `h` using `[closure_Ioi]`.

Conclude with `h hτ`.
-/
theorem slice_eq {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) {τ : ℝ} (hτ : 0 ≤ τ) : slice g τ = slice (k := k) 1 τ := by
  have hd : g.det ≠ 0 := fun h => by simpa [h] using normSq_det hg
  have c1 := continuous_slice hd
  have c2 := continuous_slice (k := k) (g := 1) (by simp)
  have hae : slice g =ᵐ[volume.restrict (Set.Ioi 0)] slice (k := k) 1 := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite c1.measurable c2.measurable
      fun s hs _ => ?_
    have h := lintegral_slice hg (s.indicator 1) (measurable_one.indicator hs)
    rw [← lintegral_indicator hs, ← lintegral_indicator hs]
    convert h using 2 <;> ext t <;> by_cases ht : t ∈ s <;> simp [ht]
  have h := (Measure.eqOn_open_of_ae_eq hae isOpen_Ioi c1.continuousOn c2.continuousOn).closure c1 c2
  rw [closure_Ioi] at h
  exact h hτ

/- English proof (translation)
Introduce `k g hg τ hτ`. Establish `h` using `slice_eq hg hτ`. Simplify `h` using `only [slice, Matrix.one_mulVec]`.
-/
theorem gaussian_slice_invariant : ∀ (k : ℕ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), gᴴ * Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) * g = Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1) → ∀ τ : ℝ, 0 ≤ τ → (∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))))))) = ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.exp (-sqLen (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2)) : Fin (k + 1) → ℂ))) := by
  intro k g hg τ hτ
  have h := slice_eq hg hτ
  simpa only [slice, Matrix.one_mulVec] using h

end GlobalTheory.HCXi.ConeSlice
