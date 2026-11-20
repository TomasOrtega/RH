import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm

open MeasureTheory Filter Topology Set

noncomputable section

def fsDens (z : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)

/- English proof (translation)
Unfold `fsDens`. Use `Real.pi_pos` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem fsDens_pos (z : ℂ) : 0 < fsDens z := by
  unfold fsDens; have := Real.pi_pos; positivity

/- English proof (translation)
Establish `hS : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}}` using `by decide`. Simplify using `only [maDens, mdisc, hS]`. Rewrite using `[Finset.sum_pair (by decide)]`. Simplify using `[hessC, levi, Matrix.det_unique]`.
-/
theorem maDens_one (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) :
    maDens φ z = 2 / Real.pi * levi (φ 0) z (Pi.single 0 1) := by
  have hS : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp only [maDens, mdisc, hS]
  rw [Finset.sum_pair (by decide)]
  simp [hessC, levi, Matrix.det_unique]

/- English proof (translation)
Use `set p0 : (Fin 1 → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj 0 with hp0`. Use `set q : (Fin 1 → ℂ) → ℝ := fun y => ‖y 0‖ ^ 2 with hqdef`. Use `set B : (Fin 1 → ℂ) →L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ) := (2 : ℝ) • ((ContinuousLinearMap.compL ℝ (Fin 1 → ℂ) ℂ ℝ).flip p0).comp ((innerSL ℝ).comp p0) with hBdef`. Establish `hB : ∀ y v, B y v = 2 * inner ℝ (y 0) (v 0)`. Introduce `y v`.

Simplify using `[hBdef, hp0]`. Establish `hq : ∀ y, HasFDerivAt q (B y) y`. Introduce `y`. Establish `h1` using `(hasStrictFDerivAt_norm_sq (y 0)).hasFDerivAt.comp y p0.hasFDerivAt`. Establish `hBy : B y = (2 • innerSL ℝ (y 0)).comp p0`.

Use extensionality with `v`. Simplify using `[hB, hp0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hBy]`. Conclude with `h1`.

Establish `hqc : Continuous q` using `by rw [hqdef]; fun_prop`. Establish `hev : ∀ᶠ y in 𝓝 z, HasDerivAt h (h' (q y)) (q y)` using `hqc.continuousAt.tendsto.eventually hd`. Establish `hfd : fderiv ℝ (fun y => h (q y)) =ᶠ[𝓝 z] fun y => h' (q y) • B y` using `by filter_upwards [hev] with y hy`. Conclude with `(hy.comp_hasFDerivAt y (hq y)).fderiv`. Express the relevant statement in the definitionally equal form `fderiv ℝ (fderiv ℝ fun y => h (q y)) z w w = _`.

Rewrite using `[hfd.fderiv_eq]`. Establish `hc : HasFDerivAt (fun y => h' (q y)) (h'' (q z) • B z) z` using `hd2.comp_hasFDerivAt z (hq z)`. Rewrite using `[HasFDerivAt.fderiv (f := fun y => h' (q y) • B y) (hc.smul B.hasFDerivAt)]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hB, real_inner_self_eq_norm_sq]`. Simplify using `only [hqdef]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_fderiv_radial (h h' h'' : ℝ → ℝ) (z : Fin 1 → ℂ)
    (hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt h (h' t) t)
    (hd2 : HasDerivAt h' (h'' (‖z 0‖ ^ 2)) (‖z 0‖ ^ 2)) (w : Fin 1 → ℂ) :
    fderiv ℝ (fderiv ℝ fun y : Fin 1 → ℂ => h (‖y 0‖ ^ 2)) z w w =
      h'' (‖z 0‖ ^ 2) * (2 * inner ℝ (z 0) (w 0)) ^ 2 + h' (‖z 0‖ ^ 2) * (2 * ‖w 0‖ ^ 2) := by
  set p0 : (Fin 1 → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj 0 with hp0
  set q : (Fin 1 → ℂ) → ℝ := fun y => ‖y 0‖ ^ 2 with hqdef
  set B : (Fin 1 → ℂ) →L[ℝ] ((Fin 1 → ℂ) →L[ℝ] ℝ) :=
    (2 : ℝ) • ((ContinuousLinearMap.compL ℝ (Fin 1 → ℂ) ℂ ℝ).flip p0).comp
      ((innerSL ℝ).comp p0) with hBdef
  have hB : ∀ y v, B y v = 2 * inner ℝ (y 0) (v 0) := by
    intro y v; simp [hBdef, hp0]
  have hq : ∀ y, HasFDerivAt q (B y) y := by
    intro y
    have h1 := (hasStrictFDerivAt_norm_sq (y 0)).hasFDerivAt.comp y p0.hasFDerivAt
    have hBy : B y = (2 • innerSL ℝ (y 0)).comp p0 := by
      ext v; simp [hB, hp0]; ring
    rw [hBy]
    exact h1
  have hqc : Continuous q := by rw [hqdef]; fun_prop
  have hev : ∀ᶠ y in 𝓝 z, HasDerivAt h (h' (q y)) (q y) :=
    hqc.continuousAt.tendsto.eventually hd
  have hfd : fderiv ℝ (fun y => h (q y)) =ᶠ[𝓝 z] fun y => h' (q y) • B y := by
    filter_upwards [hev] with y hy
    exact (hy.comp_hasFDerivAt y (hq y)).fderiv
  change fderiv ℝ (fderiv ℝ fun y => h (q y)) z w w = _
  rw [hfd.fderiv_eq]
  have hc : HasFDerivAt (fun y => h' (q y)) (h'' (q z) • B z) z :=
    hd2.comp_hasFDerivAt z (hq z)
  rw [HasFDerivAt.fderiv (f := fun y => h' (q y) • B y) (hc.smul B.hasFDerivAt)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hB, real_inner_self_eq_norm_sq]
  simp only [hqdef]
  ring

/- English proof (translation)
Rewrite using `[maDens_one]`. Unfold `levi`. Rewrite using `[hφ.fderiv.fderiv_eq, fderiv_fderiv_radial h h' h'' z hd hd2, fderiv_fderiv_radial h h' h'' z hd hd2]`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Complex.inner, norm_one, Complex.norm_I]`. Rewrite using `[← Complex.normSq_eq_norm_sq (z 0), Complex.normSq_apply]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDens_radial (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (h h' h'' : ℝ → ℝ) (z : Fin 1 → ℂ)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => h (‖y 0‖ ^ 2))
    (hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt h (h' t) t)
    (hd2 : HasDerivAt h' (h'' (‖z 0‖ ^ 2)) (‖z 0‖ ^ 2)) :
    maDens φ z = 2 / Real.pi * (h'' (‖z 0‖ ^ 2) * ‖z 0‖ ^ 2 + h' (‖z 0‖ ^ 2)) := by
  rw [maDens_one]
  unfold levi
  rw [hφ.fderiv.fderiv_eq, fderiv_fderiv_radial h h' h'' z hd hd2,
    fderiv_fderiv_radial h h' h'' z hd hd2]
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Complex.inner,
    norm_one, Complex.norm_I]
  rw [← Complex.normSq_eq_norm_sq (z 0), Complex.normSq_apply]
  simp
  ring

/- English proof (translation)
Establish `ht : 0 ≤ ‖z 0‖ ^ 2` using `by positivity`. Establish `hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt (fun t : ℝ => 1 / 2 * Real.log (1 + t)) ((2 * (1 + t))⁻¹) t` using `by filter_upwards [lt_mem_nhds (show (-1 : ℝ) < ‖z 0‖ ^ 2 by linarith)] with t ht`. Establish `h1 : (1 + t) ≠ 0` using `by linarith`. Use `(((hasDerivAt_id' t).const_add 1).log h1).const_mul (1 / 2)` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations.

Apply the tactic sequence `try simp only [Pi.mul_apply, Pi.pow_apply]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `all_goals ring`. Establish `hd2 : HasDerivAt (fun t : ℝ => (2 * (1 + t))⁻¹) (-(2 * (1 + ‖z 0‖ ^ 2) ^ 2)⁻¹) (‖z 0‖ ^ 2)`. Establish `h1 : (2 * (1 + ‖z 0‖ ^ 2)) ≠ 0` using `by positivity`.

Use `(((hasDerivAt_id' (‖z 0‖ ^ 2)).const_add 1).const_mul 2).inv h1` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Apply the tactic sequence `try simp only [Pi.mul_apply, Pi.pow_apply]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `all_goals ring`.

Rewrite using `[maDens_radial φ _ _ (fun t => -(2 * (1 + t) ^ 2)⁻¹) z hφ hd hd2, fsDens]`. Establish `h1 : (1 + ‖z 0‖ ^ 2) ≠ 0` using `by positivity`. Use `Real.pi_pos` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDens_fs (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + ‖y 0‖ ^ 2)) :
    maDens φ z = fsDens (z 0) := by
  have ht : 0 ≤ ‖z 0‖ ^ 2 := by positivity
  have hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt (fun t : ℝ => 1 / 2 * Real.log (1 + t))
      ((2 * (1 + t))⁻¹) t := by
    filter_upwards [lt_mem_nhds (show (-1 : ℝ) < ‖z 0‖ ^ 2 by linarith)] with t ht
    have h1 : (1 + t) ≠ 0 := by linarith
    have := (((hasDerivAt_id' t).const_add 1).log h1).const_mul (1 / 2)
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  have hd2 : HasDerivAt (fun t : ℝ => (2 * (1 + t))⁻¹) (-(2 * (1 + ‖z 0‖ ^ 2) ^ 2)⁻¹)
      (‖z 0‖ ^ 2) := by
    have h1 : (2 * (1 + ‖z 0‖ ^ 2)) ≠ 0 := by positivity
    have := (((hasDerivAt_id' (‖z 0‖ ^ 2)).const_add 1).const_mul 2).inv h1
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  rw [maDens_radial φ _ _ (fun t => -(2 * (1 + t) ^ 2)⁻¹) z hφ hd hd2, fsDens]
  have h1 : (1 + ‖z 0‖ ^ 2) ≠ 0 := by positivity
  have := Real.pi_pos
  field_simp
  ring

/- English proof (translation)
Establish `ht : 0 < ‖z 0‖ ^ 2` using `by positivity`. Establish `hφ' : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + (‖y 0‖ ^ 2)⁻¹)` using `by filter_upwards [hφ] with y hy`. Rewrite using `[hy, norm_inv, inv_pow]`. Establish `hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt (fun t : ℝ => 1 / 2 * Real.log (1 + t⁻¹)) (-(2 * (t * (1 + t)))⁻¹) t` using `by filter_upwards [lt_mem_nhds ht] with t ht`. Establish `h0 : t ≠ 0` using `ht.ne'`.

Establish `h1 : (1 + t⁻¹) ≠ 0` using `by positivity`. Use `(((hasDerivAt_inv h0).const_add 1).log h1).const_mul (1 / 2)` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Apply the tactic sequence `try simp only [Pi.mul_apply, Pi.pow_apply]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `all_goals ring`. Establish `hd2 : HasDerivAt (fun t : ℝ => -(2 * (t * (1 + t)))⁻¹) ((2 * ‖z 0‖ ^ 2 + 1) / (2 * (‖z 0‖ ^ 2) ^ 2 * (1 + ‖z 0‖ ^ 2) ^ 2)) (‖z 0‖ ^ 2)`. Establish `h1 : (2 * (‖z 0‖ ^ 2 * (1 + ‖z 0‖ ^ 2))) ≠ 0` using `by positivity`. Use `((((hasDerivAt_id' (‖z 0‖ ^ 2)).mul ((hasDerivAt_id' (‖z 0‖ ^ 2)).const_add 1)).const_mul 2).inv h1).neg` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations.

Apply the tactic sequence `try simp only [Pi.mul_apply, Pi.pow_apply]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `all_goals ring`. Rewrite using `[maDens_radial φ _ _ (fun t => (2 * t + 1) / (2 * t ^ 2 * (1 + t) ^ 2)) z hφ' hd hd2, fsDens]`. Establish `h1 : (1 + ‖z 0‖ ^ 2) ≠ 0` using `by positivity`.

Use `Real.pi_pos` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDens_fs_inv (φ : Fin 1 → (Fin 1 → ℂ) → ℝ) (z : Fin 1 → ℂ) (hz : z 0 ≠ 0)
    (hφ : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + ‖(y 0)⁻¹‖ ^ 2)) :
    maDens φ z = fsDens (z 0) := by
  have ht : 0 < ‖z 0‖ ^ 2 := by positivity
  have hφ' : φ 0 =ᶠ[𝓝 z] fun y => 1 / 2 * Real.log (1 + (‖y 0‖ ^ 2)⁻¹) := by
    filter_upwards [hφ] with y hy
    rw [hy, norm_inv, inv_pow]
  have hd : ∀ᶠ t in 𝓝 (‖z 0‖ ^ 2), HasDerivAt (fun t : ℝ => 1 / 2 * Real.log (1 + t⁻¹))
      (-(2 * (t * (1 + t)))⁻¹) t := by
    filter_upwards [lt_mem_nhds ht] with t ht
    have h0 : t ≠ 0 := ht.ne'
    have h1 : (1 + t⁻¹) ≠ 0 := by positivity
    have := (((hasDerivAt_inv h0).const_add 1).log h1).const_mul (1 / 2)
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  have hd2 : HasDerivAt (fun t : ℝ => -(2 * (t * (1 + t)))⁻¹)
      ((2 * ‖z 0‖ ^ 2 + 1) / (2 * (‖z 0‖ ^ 2) ^ 2 * (1 + ‖z 0‖ ^ 2) ^ 2)) (‖z 0‖ ^ 2) := by
    have h1 : (2 * (‖z 0‖ ^ 2 * (1 + ‖z 0‖ ^ 2))) ≠ 0 := by positivity
    have := ((((hasDerivAt_id' (‖z 0‖ ^ 2)).mul
      ((hasDerivAt_id' (‖z 0‖ ^ 2)).const_add 1)).const_mul 2).inv h1).neg
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  rw [maDens_radial φ _ _ (fun t => (2 * t + 1) / (2 * t ^ 2 * (1 + t) ^ 2)) z hφ' hd hd2, fsDens]
  have h1 : (1 + ‖z 0‖ ^ 2) ≠ 0 := by positivity
  have := Real.pi_pos
  field_simp
  ring

/- English proof (translation)
Establish `hπ` using `Real.pi_pos`. Establish `key` using `integral_Ioi_of_hasDerivAt_of_nonneg (a := 0) (l := 0) (g := fun r : ℝ => -(2 * Real.pi * (1 + r ^ 2))⁻¹) (g' := fun r : ℝ => r * (1 / (Real.pi * (1 + r ^ 2) ^ 2))) (by fun_prop (disch := positivity)) ?_ ?_ ?_`. Rewrite using `[key]`. Simplify using the standard rewrite rules. Introduce `r _`.

Establish `h1 : (2 * Real.pi * (1 + r ^ 2)) ≠ 0` using `by positivity`. Use `((((hasDerivAt_id' r).pow 2).const_add 1).const_mul (2 * Real.pi)).inv h1 |>.neg` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Apply the tactic sequence `try simp only [Pi.mul_apply, Pi.pow_apply]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `all_goals ring`. Introduce `r hr`. Establish `: (0 : ℝ) < r` using `hr`. Check the signs of the components of the expression. Establish `h1 : Tendsto (fun r : ℝ => 2 * Real.pi * (1 + r ^ 2)) atTop atTop`.

Apply `Tendsto.const_mul_atTop (by positivity)` to reduce the goal to its premises. Conclude with `tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)`. Simplify using `using (tendsto_inv_atTop_zero.comp h1).neg`.
-/
theorem integral_Ioi_fsDens_radial :
    ∫ r in Ioi (0 : ℝ), r * (1 / (Real.pi * (1 + r ^ 2) ^ 2)) = 1 / (2 * Real.pi) := by
  have hπ := Real.pi_pos
  have key := integral_Ioi_of_hasDerivAt_of_nonneg (a := 0) (l := 0)
    (g := fun r : ℝ => -(2 * Real.pi * (1 + r ^ 2))⁻¹)
    (g' := fun r : ℝ => r * (1 / (Real.pi * (1 + r ^ 2) ^ 2)))
    (by fun_prop (disch := positivity)) ?_ ?_ ?_
  · rw [key]; simp
  · intro r _
    have h1 : (2 * Real.pi * (1 + r ^ 2)) ≠ 0 := by positivity
    have := ((((hasDerivAt_id' r).pow 2).const_add 1).const_mul (2 * Real.pi)).inv h1 |>.neg
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  · intro r hr
    have : (0 : ℝ) < r := hr
    positivity
  · have h1 : Tendsto (fun r : ℝ => 2 * Real.pi * (1 + r ^ 2)) atTop atTop := by
      apply Tendsto.const_mul_atTop (by positivity)
      exact tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    simpa using (tendsto_inv_atTop_zero.comp h1).neg

/- English proof (translation)
Rewrite using `[← Complex.integral_comp_polarCoord_symm, polarCoord_target]`. Establish `hf : ∀ p : ℝ × ℝ, p.1 • fsDens (Complex.polarCoord.symm p) = p.1 * (1 / (Real.pi * (1 + p.1 ^ 2) ^ 2)) * 1`. Introduce `p`. Simplify using `[fsDens, sq_abs]`. Repeatedly rewrite using `[hf]`.

Rewrite using `[Measure.volume_eq_prod, setIntegral_prod_mul (fun r : ℝ => r * (1 / (Real.pi * (1 + r ^ 2) ^ 2))) (fun _ => (1 : ℝ)), integral_Ioi_fsDens_radial]`. Establish `hπ` using `Real.pi_pos`. Rewrite using `[integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le (by linarith)]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_fsDens : ∫ z : ℂ, fsDens z = 1 := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hf : ∀ p : ℝ × ℝ, p.1 • fsDens (Complex.polarCoord.symm p) =
      p.1 * (1 / (Real.pi * (1 + p.1 ^ 2) ^ 2)) * 1 := by
    intro p
    simp [fsDens, sq_abs]
  simp_rw [hf]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun r : ℝ => r * (1 / (Real.pi * (1 + r ^ 2) ^ 2))) (fun _ => (1 : ℝ)),
    integral_Ioi_fsDens_radial]
  have hπ := Real.pi_pos
  rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le (by linarith)]
  simp
  field_simp
  ring

/- English proof (translation)
The claim follows from `.of_integral_ne_zero (by rw [integral_fsDens]; exact one_ne_zero)`.
-/
theorem integrable_fsDens : Integrable fsDens :=
  .of_integral_ne_zero (by rw [integral_fsDens]; exact one_ne_zero)

/- English proof (translation)
Establish `hs : MeasurableSet ({0}ᶜ : Set ℂ)` using `(measurableSet_singleton 0).compl`. Establish `himg : (fun z : ℂ => z⁻¹) '' ({0}ᶜ : Set ℂ) = {0}ᶜ`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`.

Simplify using `using hw`. Introduce `hz; exact ⟨z⁻¹, by simpa using hz, inv_inv z⟩`. Establish `hder : ∀ z ∈ ({0}ᶜ : Set ℂ), HasFDerivWithinAt (fun z : ℂ => z⁻¹) (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹))).restrictScalars ℝ) ({0}ᶜ) z`. Introduce `z hz`. Conclude with `((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`.

Establish `hcv` using `integral_image_eq_integral_abs_det_fderiv_smul volume hs hder inv_injective.injOn (fun z => g z * fsDens z)`. Rewrite `hcv` using `[himg]`. Establish `hnull : ∀ F : ℂ → ℝ, ∫ z in ({0}ᶜ : Set ℂ), F z = ∫ z, F z` using `fun F => by`. Rewrite using `[restrict_compl_singleton]`. Rewrite `hcv` using `[hnull, hnull]`.

Rewrite using `[hcv]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with z hz`. Establish `hz0 : z ≠ 0` using `hz`. Establish `hdet : (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹))).restrictScalars ℝ).det = ‖z‖⁻¹ ^ 4`.

Simplify using `[ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul]`. Rewrite using `[hdet, smul_eq_mul, fsDens, fsDens, norm_inv]`. Establish `h1 : ‖z‖ ≠ 0` using `norm_ne_zero_iff.mpr hz0`. Use `Real.pi_pos` as an intermediate fact. Rewrite using `[abs_of_nonneg (by positivity)]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_fsDens_inv (g : ℂ → ℝ) :
    ∫ z, g z⁻¹ * fsDens z = ∫ z, g z * fsDens z := by
  have hs : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have himg : (fun z : ℂ => z⁻¹) '' ({0}ᶜ : Set ℂ) = {0}ᶜ := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; simpa using hw
    · intro hz; exact ⟨z⁻¹, by simpa using hz, inv_inv z⟩
  have hder : ∀ z ∈ ({0}ᶜ : Set ℂ), HasFDerivWithinAt (fun z : ℂ => z⁻¹)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹))).restrictScalars ℝ)
      ({0}ᶜ) z := by
    intro z hz
    exact ((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hs hder
    inv_injective.injOn (fun z => g z * fsDens z)
  rw [himg] at hcv
  have hnull : ∀ F : ℂ → ℝ, ∫ z in ({0}ᶜ : Set ℂ), F z = ∫ z, F z := fun F => by
    rw [restrict_compl_singleton]
  rw [hnull, hnull] at hcv
  rw [hcv]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with z hz
  have hz0 : z ≠ 0 := hz
  have hdet : (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z ^ 2)⁻¹))).restrictScalars
      ℝ).det = ‖z‖⁻¹ ^ 4 := by
    simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
      Complex.normSq_eq_norm_sq, ← pow_mul]
  rw [hdet, smul_eq_mul, fsDens, fsDens, norm_inv]
  have h1 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have := Real.pi_pos
  rw [abs_of_nonneg (by positivity)]
  field_simp
  ring

end

end ReciprocityTheory.AnForm
