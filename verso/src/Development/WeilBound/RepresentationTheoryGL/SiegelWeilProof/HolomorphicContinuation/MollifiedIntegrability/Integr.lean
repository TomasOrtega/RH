import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR.I

open PositivityTheory.Rg.Sw

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_ofNat]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [herm, Complex.normSq_apply]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normSq_herm (y : E n) (i j : Fin n) :
    Complex.normSq (herm y i j) = (y i j ^ 2 + y j i ^ 2) / 2 := by
  simp only [herm, Complex.normSq_apply]
  simp
  ring

/- English proof (translation)
Repeatedly rewrite using `[normSq_herm, ← Finset.sum_div, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm (f := fun i j => y j i ^ 2)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_normSq_herm (y : E n) :
    ∑ i, ∑ j, Complex.normSq (herm y i j) = ∑ a, ∑ b, y a b ^ 2 := by
  simp_rw [normSq_herm, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => y j i ^ 2)]
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.prod_insert hj]`. Establish `h0 : 0 ≤ ∑ i ∈ s, a i` using `Finset.sum_nonneg fun i _ => ha i`.

Use polynomial arithmetic with `[ha j]`.
-/
theorem one_add_sum_le_prod (s : Finset (Fin n)) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have h0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
    nlinarith [ha j]

/- English proof (translation)
Use `set hA := herm_isHermitian y`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Use `set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD`. Establish `hUs : star U * U = 1` using `Unitary.coe_star_mul_self _`. Establish `hsU : U * star U = 1` using `Unitary.coe_mul_star_self _`.

Establish `hspec : herm y = U * D * star U`. Use `hA.spectral_theorem` as an intermediate fact. Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `this`. Establish `hsq : 1 + herm y * herm y = U * (1 + D * D) * star U`.

Rewrite using `[hspec]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]`. Rewrite using `[hsU]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]`.

Establish `hDD : 1 + D * D = diagonal fun i => ((1 + hA.eigenvalues i ^ 2 : ℝ) : ℂ)`. Rewrite using `[hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[pow_two]`.

Establish `hdetU : U.det * (star U).det = 1` using `by rw [← det_mul, hsU, det_one]`. Prove the components needed by the constructor for the conclusion. Unfold `dP`. Rewrite using `[hsq, det_mul, det_mul, hDD, det_diagonal]`. Rewrite using `[mul_comm U.det, mul_assoc, hdetU, mul_one, ← Complex.ofReal_prod, Complex.ofReal_re]`.

Establish `hsq2 : herm y * herm y = U * (D * D) * star U`. Rewrite using `[hspec]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]`. Establish `htr : (herm y * herm y).trace = ∑ i, ((hA.eigenvalues i ^ 2 : ℝ) : ℂ)`.

Rewrite using `[hsq2, trace_mul_comm, ← Matrix.mul_assoc, hUs, Matrix.one_mul, hD, diagonal_mul_diagonal, trace_diagonal]`. Simplify using `[pow_two]`. Establish `hre : (herm y * herm y).trace.re = ∑ i, ∑ j, Complex.normSq (herm y i j)`. Rewrite using `[trace]`. Simplify using `only [diag_apply, mul_apply, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hji : herm y j i = star (herm y i j)`. Use `congrFun (congrFun hA.eq j) i` as an intermediate fact. Rewrite `this` using `[conjTranspose_apply]`. Conclude with `this.symm`.

Rewrite using `[hji, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]`. Rewrite using `[← sum_normSq_herm, ← hre, htr, Complex.re_sum]`. Simplify using `only [Complex.ofReal_re]`.
-/
theorem dP_eq_prod (y : E n) :
    dP y = ∏ i, (1 + (herm_isHermitian y).eigenvalues i ^ 2) ∧
      ∑ a, ∑ b, y a b ^ 2 = ∑ i, (herm_isHermitian y).eigenvalues i ^ 2 := by
  set hA := herm_isHermitian y
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hUs : star U * U = 1 := Unitary.coe_star_mul_self _
  have hsU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : herm y = U * D * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hsq : 1 + herm y * herm y = U * (1 + D * D) * star U := by
    rw [hspec]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [hsU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
  have hDD : 1 + D * D = diagonal fun i => ((1 + hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    funext i
    simp [pow_two]
  have hdetU : U.det * (star U).det = 1 := by rw [← det_mul, hsU, det_one]
  constructor
  · unfold dP
    rw [hsq, det_mul, det_mul, hDD, det_diagonal]
    rw [mul_comm U.det, mul_assoc, hdetU, mul_one, ← Complex.ofReal_prod, Complex.ofReal_re]
  · have hsq2 : herm y * herm y = U * (D * D) * star U := by
      rw [hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUs, Matrix.one_mul]
    have htr : (herm y * herm y).trace = ∑ i, ((hA.eigenvalues i ^ 2 : ℝ) : ℂ) := by
      rw [hsq2, trace_mul_comm, ← Matrix.mul_assoc, hUs, Matrix.one_mul, hD, diagonal_mul_diagonal, trace_diagonal]
      simp [pow_two]
    have hre : (herm y * herm y).trace.re = ∑ i, ∑ j, Complex.normSq (herm y i j) := by
      rw [trace]
      simp only [diag_apply, mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hji : herm y j i = star (herm y i j) := by
        have := congrFun (congrFun hA.eq j) i
        rw [conjTranspose_apply] at this
        exact this.symm
      rw [hji, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    rw [← sum_normSq_herm, ← hre, htr, Complex.re_sum]
    simp only [Complex.ofReal_re]

/- English proof (translation)
Take `⟨h1, h2⟩` from `dP_eq_prod y`. Rewrite using `[h1, h2]`. Conclude with `one_add_sum_le_prod _ _ fun i => sq_nonneg _`.
-/
theorem dP_ge (y : E n) : 1 + ∑ a, ∑ b, y a b ^ 2 ≤ dP y := by
  obtain ⟨h1, h2⟩ := dP_eq_prod y
  rw [h1, h2]
  exact one_add_sum_le_prod _ _ fun i => sq_nonneg _

/- English proof (translation)
Establish `h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2` using `Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _`. Combine the linear relations using `[dP_ge y]`.
-/
theorem dP_pos (y : E n) : 0 < dP y := by
  have h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  linarith [dP_ge y]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Unfold `herm`. Use `fun_prop`.
-/
theorem continuous_herm : Continuous (herm : E n → Matrix (Fin n) (Fin n) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold herm
  fun_prop

/- English proof (translation)
Unfold `dP`. Establish `: Continuous fun y : E n => 1 + herm y * herm y` using `continuous_const.add (continuous_herm.matrix_mul continuous_herm)`. Conclude with `Complex.continuous_re.comp this.matrix_det`.
-/
theorem continuous_dP : Continuous (dP : E n → ℝ) := by
  unfold dP
  have : Continuous fun y : E n => 1 + herm y * herm y := continuous_const.add (continuous_herm.matrix_mul continuous_herm)
  exact Complex.continuous_re.comp this.matrix_det

/- English proof (translation)
Establish `h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2` using `Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _`. Establish `hle : ‖y‖ ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2)`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`.

Use `Real.abs_le_sqrt ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sq_le_sum (y : E n) : ‖y‖ ^ 2 ≤ ∑ a, ∑ b, y a b ^ 2 := by
  have h0 : 0 ≤ ∑ a, ∑ b, y a b ^ 2 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hle : ‖y‖ ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun b => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    calc y a b ^ 2 ≤ ∑ b', y a b' ^ 2 := Finset.single_le_sum (fun b' _ => sq_nonneg (y a b')) (Finset.mem_univ b)
      _ ≤ ∑ a', ∑ b', y a' b' ^ 2 :=
        Finset.single_le_sum (f := fun a' => ∑ b', y a' b' ^ 2) (fun a' _ => Finset.sum_nonneg fun b' _ => sq_nonneg _)
          (Finset.mem_univ a)
  calc ‖y‖ ^ 2 ≤ Real.sqrt (∑ a, ∑ b, y a b ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := Real.sq_sqrt h0

/- English proof (translation)
Introduce `n`. Use `⟨⟨1, one_pos, fun y => by simpa using dP_ge y⟩, fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `hfin : (Module.finrank ℝ (E n) : ℝ) = (n : ℝ) ^ 2`. Establish `h : Module.finrank ℝ (Fin n → Fin n → ℝ) = n * n`. Rewrite using `[Module.finrank_pi_fintype]`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `((Module.finrank ℝ (Fin n → Fin n → ℝ) : ℕ) : ℝ) = (n : ℝ) ^ 2`. Rewrite using `[h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hr : (Module.finrank ℝ (E n) : ℝ) < 2 * σ` using `by rw [hfin]; linarith`. Establish `hint` using `integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (E n))) hr`. Establish `hσ0 : 0 ≤ σ` using `by nlinarith [sq_nonneg (n : ℝ)]`. Use `hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Conclude with `(continuous_dP.rpow_const fun y => Or.inl (dP_pos y).ne').aestronglyMeasurable`.

Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dP_pos y).le _)]`. Establish `h1 : 1 + ‖y‖ ^ 2 ≤ dP y` using `by linarith [norm_sq_le_sum y, dP_ge y]`. Establish `h2 : 0 < 1 + ‖y‖ ^ 2` using `by positivity`. Rewrite using `[show -(2 * σ) / 2 = -σ by ring]`. Conclude with `Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)`.
-/
theorem integr : Integr := by
  intro n
  refine ⟨⟨1, one_pos, fun y => by simpa using dP_ge y⟩, fun σ hσ => ?_⟩
  have hfin : (Module.finrank ℝ (E n) : ℝ) = (n : ℝ) ^ 2 := by
    have h : Module.finrank ℝ (Fin n → Fin n → ℝ) = n * n := by
      rw [Module.finrank_pi_fintype]
      simp
    change ((Module.finrank ℝ (Fin n → Fin n → ℝ) : ℕ) : ℝ) = (n : ℝ) ^ 2
    rw [h]
    push_cast
    ring
  have hr : (Module.finrank ℝ (E n) : ℝ) < 2 * σ := by rw [hfin]; linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (E n))) hr
  have hσ0 : 0 ≤ σ := by nlinarith [sq_nonneg (n : ℝ)]
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (continuous_dP.rpow_const fun y => Or.inl (dP_pos y).ne').aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dP_pos y).le _)]
    have h1 : 1 + ‖y‖ ^ 2 ≤ dP y := by linarith [norm_sq_le_sum y, dP_ge y]
    have h2 : 0 < 1 + ‖y‖ ^ 2 := by positivity
    rw [show -(2 * σ) / 2 = -σ by ring]
    exact Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)

end PositivityTheory.Rg.Sw.WR.I
