import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

variable {ι : Type*} [Fintype ι]

def fsLp (ι : Type*) [Fintype ι] : (ι → ℂ) →L[ℝ] EuclideanSpace ℂ ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm :
    (ι → ℂ) →L[ℂ] EuclideanSpace ℂ ι).restrictScalars ℝ

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma fsLp_apply (z : ι → ℂ) : fsLp ι z = WithLp.toLp 2 z := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
lemma fsLp_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : fsLp ι z ≠ 0 := by
  rw [fsLp_apply]
  intro h
  apply hz
  have h2 := congrArg (WithLp.ofLp (p := 2)) h
  simpa using h2

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma fsLp_smul_I (w : ι → ℂ) : fsLp ι (Complex.I • w) = Complex.I • fsLp ι w := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma fsLp_normSq_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : ‖fsLp ι z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (fsLp_ne_zero hz))

def fsGrad (y : ι → ℂ) : (ι → ℂ) →L[ℝ] ℝ :=
  (‖fsLp ι y‖ ^ 2)⁻¹ • (innerSL ℝ (fsLp ι y)).comp (fsLp ι)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma fsGrad_apply (y v : ι → ℂ) :
    fsGrad y v = (‖fsLp ι y‖ ^ 2)⁻¹ * inner ℝ (fsLp ι y) (fsLp ι v) := rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasFDerivAt_logFs {y : ι → ℂ} (hy : y ≠ 0) :
    HasFDerivAt (fun z => Real.log ‖fsLp ι z‖) (fsGrad y) y := by
  have h0 : fsLp ι y ≠ 0 := fsLp_ne_zero hy
  have hL : HasFDerivAt (fsLp ι) (fsLp ι) y := (fsLp ι).hasFDerivAt
  have h1 := (HasFDerivAt.log (HasFDerivAt.norm_sq hL) (fsLp_normSq_ne_zero hy)).const_mul (1 / 2 : ℝ)
  have hfun : (fun z => Real.log ‖fsLp ι z‖) = fun z => 1 / 2 * Real.log (‖fsLp ι z‖ ^ 2) := by
    funext z
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun]
  refine h1.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  rw [fsGrad_apply]
  simp
  ring

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma fderiv_logFs_eventuallyEq {z : ι → ℂ} (hz : z ≠ 0) :
    fderiv ℝ (fun z => Real.log ‖fsLp ι z‖) =ᶠ[nhds z] fsGrad := by
  filter_upwards [eventually_ne_nhds hz] with y hy using (hasFDerivAt_logFs hy).fderiv

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma differentiableAt_fsGrad {z : ι → ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℝ (fsGrad (ι := ι)) z := by
  show DifferentiableAt ℝ
    (fun y => (‖fsLp ι y‖ ^ 2)⁻¹ • (innerSL ℝ (fsLp ι y)).comp (fsLp ι)) z
  have h1 : DifferentiableAt ℝ (fun y => (‖fsLp ι y‖ ^ 2)⁻¹) z :=
    (DifferentiableAt.norm_sq ℂ (fsLp ι).differentiableAt).inv (fsLp_normSq_ne_zero hz)
  have h2 : DifferentiableAt ℝ (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι)) z :=
    (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))).differentiableAt
  exact h1.smul h2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma hess_logFs {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => Real.log ‖fsLp ι z‖)) z w w =
      ‖fsLp ι w‖ ^ 2 / ‖fsLp ι z‖ ^ 2 -
        2 * inner ℝ (fsLp ι z) (fsLp ι w) ^ 2 / (‖fsLp ι z‖ ^ 2) ^ 2 := by
  have hL : HasFDerivAt (fsLp ι) (fsLp ι) z := (fsLp ι).hasFDerivAt
  have h0 := fsLp_normSq_ne_zero hz
  have hc := (hasDerivAt_inv h0).comp_hasFDerivAt z (HasFDerivAt.norm_sq hL)
  have hT : HasFDerivAt (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι))
      (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))) z :=
    (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))).hasFDerivAt
  have hG := HasFDerivAt.smul hc hT
  rw [(fderiv_logFs_eventuallyEq hz).fderiv_eq]
  have hfG : (fsGrad (ι := ι)) = ((fun y : ℝ => y⁻¹) ∘ fun x => ‖fsLp ι x‖ ^ 2) •
      (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι)) := rfl
  rw [hfG, hG.fderiv]
  simp
  field_simp
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Treat this case separately.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
lemma inner_sq_add_inner_I_sq (x y : EuclideanSpace ℂ ι) :
    inner ℝ x y ^ 2 + inner ℝ x (Complex.I • y) ^ 2 = ‖inner ℂ x y‖ ^ 2 := by
  have e0 : ∀ u v : EuclideanSpace ℂ ι, inner ℝ u v = (inner ℂ u v).re := by
    intro u v
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    first
    | rfl
    | simp [Complex.inner, RCLike.inner_apply]
    | simp [Complex.inner, mul_comm]
  rw [e0, e0, inner_smul_right, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.I_re, Complex.I_im]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Establish an intermediate fact. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem fsMetric_isSmooth : IsSmoothMetric (fsMetric ι) := by
  intro z hz
  change ContDiffWithinAt ℝ _ (fun z => ‖fsLp ι z‖) _ z
  have h0 : fsLp ι z ≠ 0 := fsLp_ne_zero hz
  have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℂ ι => ‖u‖) (fsLp ι z) := by
    first
    | exact contDiffAt_norm ℝ h0
    | exact contDiffAt_norm h0
  exact (hn.comp z (fsLp ι).contDiff.contDiffAt).contDiffWithinAt

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviForm_fsMetric {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    leviForm (fun z => Real.log ((fsMetric ι).ρ z)) z w =
      (‖fsLp ι w‖ ^ 2 * ‖fsLp ι z‖ ^ 2 - ‖inner ℂ (fsLp ι z) (fsLp ι w)‖ ^ 2) /
        (2 * (‖fsLp ι z‖ ^ 2) ^ 2) := by
  change leviForm (fun z => Real.log ‖fsLp ι z‖) z w = _
  unfold leviForm
  rw [hess_logFs hz, hess_logFs hz, fsLp_smul_I, norm_smul, Complex.norm_I, one_mul,
    ← inner_sq_add_inner_I_sq]
  have h0 := fsLp_normSq_ne_zero hz
  field_simp
  ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Use the polynomial consequences of the given equalities and inequalities. Check the signs of the components of the expression.
-/
theorem fsMetric_isSemipositive : IsSemipositive (fsMetric ι) := by
  refine ⟨fsMetric_isSmooth, fun z hz w => ?_⟩
  rw [leviForm_fsMetric hz]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (fsLp ι z) (fsLp ι w)
  have h2 := mul_self_le_mul_self (norm_nonneg _) hcs
  apply div_nonneg
  · nlinarith [h2]
  · positivity

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fsMetric_fin_isSemipositive (n : ℕ) : IsSemipositive (fsMetric (Fin n)) := fsMetric_isSemipositive

end ReciprocityTheory.ChartRestriction.G.Geo
