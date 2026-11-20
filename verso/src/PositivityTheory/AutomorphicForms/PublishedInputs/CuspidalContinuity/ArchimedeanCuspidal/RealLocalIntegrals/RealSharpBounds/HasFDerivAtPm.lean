import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.B

namespace Ibp

/- English proof (translation)
Establish `hχm : AEStronglyMeasurable χ volume` using `hχ.continuous.aestronglyMeasurable`. Establish `hint : ∀ k, Integrable (D k) → Integrable (fun x => D k x * χ x)` using `fun k hk => hk.mul_bdd hχm (c := 1) (Filter.Eventually.of_forall fun x => (hχn x).le)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro _`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `hI`. Establish `h1 : Integrable (D n)` using `hI n (Nat.le_succ n)`. Establish `h2 : Integrable (D (n + 1))` using `hI (n + 1) le_rfl`.

Establish `e1 : ∫ x, D n x * fderiv ℝ χ x v = - ∫ x, fderiv ℝ (D n) x v * χ x`. Apply `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` to reduce the goal to its premises. Repeatedly rewrite using `[hDv]`. Conclude with `hint _ h2`. Repeatedly rewrite using `[hχv]`.

Use `(hint _ h1).const_mul a` as an intermediate fact. Use `this.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hint _ h1`.

Conclude with `fun x _ => (hD n).differentiableAt`. Conclude with `fun x _ => hχ.differentiableAt`. Establish `e2 : ∫ x, D n x * fderiv ℝ χ x v = a * ∫ x, D n x * χ x`. Repeatedly rewrite using `[hχv]`. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e1` using `[hDv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ibp_iter (D : ℕ → (Fin 2 → ℝ) → ℂ) (χ : (Fin 2 → ℝ) → ℂ) (v : Fin 2 → ℝ) (a : ℂ)
    (hD : ∀ k, Differentiable ℝ (D k)) (hDv : ∀ k x, fderiv ℝ (D k) x v = D (k + 1) x)
    (hχ : Differentiable ℝ χ) (hχv : ∀ x, fderiv ℝ χ x v = a * χ x) (hχn : ∀ x, ‖χ x‖ = 1) :
    ∀ n : ℕ, (∀ k ≤ n, Integrable (D k)) →
      a ^ n * ∫ x, D 0 x * χ x = (-1) ^ n * ∫ x, D n x * χ x := by
  have hχm : AEStronglyMeasurable χ volume := hχ.continuous.aestronglyMeasurable
  have hint : ∀ k, Integrable (D k) → Integrable (fun x => D k x * χ x) := fun k hk =>
    hk.mul_bdd hχm (c := 1) (Filter.Eventually.of_forall fun x => (hχn x).le)
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hI
    have h1 : Integrable (D n) := hI n (Nat.le_succ n)
    have h2 : Integrable (D (n + 1)) := hI (n + 1) le_rfl
    have e1 : ∫ x, D n x * fderiv ℝ χ x v = - ∫ x, fderiv ℝ (D n) x v * χ x := by
      apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      · simp_rw [hDv]; exact hint _ h2
      · simp_rw [hχv]
        have := (hint _ h1).const_mul a
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only; ring
      · exact hint _ h1
      · exact fun x _ => (hD n).differentiableAt
      · exact fun x _ => hχ.differentiableAt
    have e2 : ∫ x, D n x * fderiv ℝ χ x v = a * ∫ x, D n x * χ x := by
      simp_rw [hχv]
      rw [← integral_const_mul]
      congr 1; funext x; ring
    simp_rw [hDv] at e1
    calc a ^ (n + 1) * ∫ x, D 0 x * χ x = a * (a ^ n * ∫ x, D 0 x * χ x) := by ring
      _ = a * ((-1) ^ n * ∫ x, D n x * χ x) := by rw [ih fun k hk => hI k (hk.trans (Nat.le_succ n))]
      _ = (-1) ^ n * (a * ∫ x, D n x * χ x) := by ring
      _ = (-1) ^ (n + 1) * ∫ x, D (n + 1) x * χ x := by rw [← e2, e1]; ring

/- English proof (translation)
Use `ibp_iter D χ v a hD hDv hχ hχv hχn n hI` as an intermediate fact. Establish `h` using `congrArg norm this`. Rewrite `h` using `[norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Rewrite using `[h]`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[norm_mul, hχn, mul_one]`.
-/
theorem ibp_norm (D : ℕ → (Fin 2 → ℝ) → ℂ) (χ : (Fin 2 → ℝ) → ℂ) (v : Fin 2 → ℝ) (a : ℂ)
    (hD : ∀ k, Differentiable ℝ (D k)) (hDv : ∀ k x, fderiv ℝ (D k) x v = D (k + 1) x)
    (hχ : Differentiable ℝ χ) (hχv : ∀ x, fderiv ℝ χ x v = a * χ x) (hχn : ∀ x, ‖χ x‖ = 1)
    (n : ℕ) (hI : ∀ k ≤ n, Integrable (D k)) :
    ‖a‖ ^ n * ‖∫ x, D 0 x * χ x‖ ≤ ∫ x, ‖D n x‖ := by
  have := ibp_iter D χ v a hD hDv hχ hχv hχn n hI
  have h := congrArg norm this
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul] at h
  rw [h]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x; rw [norm_mul, hχn, mul_one]

def Pm (h : M22) (x : Fin 2 → ℝ) : M23 := Matrix.of.symm (Matrix.of h * blk x)

def Lh (h : M22) : (Fin 2 → ℝ) →ₗ[ℝ] M23 where
  toFun x := fun i j => if j = 2 then (Matrix.of h *ᵥ x) i else 0
  map_add' x y := by
    ext i j; by_cases hj : j = 2 <;> simp [hj, Matrix.mulVec_add]
  map_smul' c x := by
    ext i j; by_cases hj : j = 2 <;> simp [hj, Matrix.mulVec_smul]

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;>`. Simplify using `[Pm, blk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]`.
-/
theorem Pm_apply (h : M22) (x : Fin 2 → ℝ) (i : Fin 2) :
    Pm h x i 0 = h i 0 ∧ Pm h x i 1 = h i 1 ∧ Pm h x i 2 = (Matrix.of h *ᵥ x) i := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Pm, blk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use extensionality with `i j`. Take `⟨a0, a1, a2⟩` from `Pm_apply h x i`. Take `⟨b0, b1, b2⟩` from `Pm_apply h 0 i`. Use `fin_cases j`.

Simplify using `[Lh, a0, b0]`. Simplify using `[Lh, a1, b1]`. Simplify using `[Lh, a2, b2]`.
-/
theorem Pm_eq (h : M22) : Pm h = fun x => Pm h 0 + Lh h x := by
  funext x; ext i j
  obtain ⟨a0, a1, a2⟩ := Pm_apply h x i
  obtain ⟨b0, b1, b2⟩ := Pm_apply h 0 i
  fin_cases j
  · simp [Lh, a0, b0]
  · simp [Lh, a1, b1]
  · simp [Lh, a2, b2]

/- English proof (translation)
Rewrite using `[Pm_eq]`. Conclude with `(LinearMap.toContinuousLinearMap (Lh h)).hasFDerivAt.const_add _`.
-/
theorem hasFDerivAt_Pm (h : M22) (x : Fin 2 → ℝ) :
    HasFDerivAt (Pm h) (LinearMap.toContinuousLinearMap (Lh h)) x := by
  rw [Pm_eq]
  exact (LinearMap.toContinuousLinearMap (Lh h)).hasFDerivAt.const_add _

/- English proof (translation)
Establish `a` using `fun i => Pm_apply h x i`. Establish `e : ∀ i (j : Fin 3), ‖Pm h x i j‖ ≤ ‖Pm h x‖` using `fun i j => (norm_le_pi_norm (Pm h x i) j).trans (norm_le_pi_norm (Pm h x) i)`. Prove the components needed by the constructor for the conclusion. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_` and prove the remaining obligations.

Use `fin_cases j`. Simplify `e i 0` using `[(a i).1]`. Simplify `e i 1` using `[(a i).2.1]`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Simplify `e i 2` using `[(a i).2.2]`.
-/
theorem norm_le_Pm (h : M22) (x : Fin 2 → ℝ) :
    ‖h‖ ≤ ‖Pm h x‖ ∧ ‖Matrix.of h *ᵥ x‖ ≤ ‖Pm h x‖ := by
  have a := fun i => Pm_apply h x i
  have e : ∀ i (j : Fin 3), ‖Pm h x i j‖ ≤ ‖Pm h x‖ := fun i j =>
    (norm_le_pi_norm (Pm h x i) j).trans (norm_le_pi_norm (Pm h x) i)
  constructor
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    fin_cases j
    · simpa [(a i).1] using e i 0
    · simpa [(a i).2.1] using e i 1
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    simpa [(a i).2.2] using e i 2

/- English proof (translation)
The claim follows from `|(Matrix.of h).det|⁻¹ * ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(8 : ℝ)) := by set f := Matrix.toLin' (Matrix.of h) have hf : LinearMap.det f ≠ 0 := by rwa [LinearMap.det_toLin'] have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin 2 → ℝ)) hf set g : (Fin 2 → …`.
-/
theorem cov (h : M22) (hdet : (Matrix.of h).det ≠ 0) :
    Integrable (fun x : Fin 2 → ℝ => (1 + ‖Matrix.of h *ᵥ x‖) ^ (-(8 : ℝ))) ∧
    ∫ x : Fin 2 → ℝ, (1 + ‖Matrix.of h *ᵥ x‖) ^ (-(8 : ℝ)) =
      |(Matrix.of h).det|⁻¹ * ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(8 : ℝ)) := by
  set f := Matrix.toLin' (Matrix.of h)
  have hf : LinearMap.det f ≠ 0 := by rwa [LinearMap.det_toLin']
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin 2 → ℝ)) hf
  set g : (Fin 2 → ℝ) → ℝ := fun y => (1 + ‖y‖) ^ (-(8 : ℝ))
  have hgi : Integrable g := integrable_one_add_norm (by simp; norm_num)
  have hfm : Measurable f := (LinearMap.continuous_of_finiteDimensional f).measurable
  have hpos : ∀ y : Fin 2 → ℝ, (1 + ‖y‖) ≠ 0 := fun y => by positivity
  have hgc : Continuous g :=
    (continuous_const.add continuous_norm).rpow_const fun y => Or.inl (hpos y)
  have hgm : AEStronglyMeasurable g (Measure.map f volume) := hgc.aestronglyMeasurable
  have eq : (fun x : Fin 2 → ℝ => (1 + ‖Matrix.of h *ᵥ x‖) ^ (-(8 : ℝ))) = g ∘ f := by
    funext x; simp [g, f, Matrix.toLin'_apply]
  constructor
  · rw [eq, ← integrable_map_measure hgm hfm.aemeasurable, hmap]
    exact hgi.smul_measure ENNReal.ofReal_ne_top
  · rw [eq, Function.comp_def, ← integral_map hfm.aemeasurable hgm, hmap, integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _), LinearMap.det_toLin', abs_inv, smul_eq_mul]

/- English proof (translation)
Take `⟨h1, h2⟩` from `norm_le_Pm h x`. Establish `hA : ‖iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)‖ ≤ ‖iteratedFDeriv ℝ n Ψ (Pm h x)‖`. Use `((iteratedFDeriv ℝ n Ψ (Pm h x)).le_opNorm _).trans ?_` and prove the remaining obligations. Use `mul_le_of_le_one_right (norm_nonneg _) ?_` and prove the remaining obligations. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hE)`.

Establish `hP : (1 + ‖h‖) ^ N * (1 + ‖Matrix.of h *ᵥ x‖) ^ 8 ≤ (1 + ‖Pm h x‖) ^ (N + 8)`. Rewrite using `[pow_add]`. Use `gcongr`. Establish `key : ‖iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)‖ * ((1 + ‖h‖) ^ N * (1 + ‖Matrix.of h *ᵥ x‖) ^ 8) ≤ B`. Combine the equalities or inequalities in the displayed calculation.

Establish `e8 : (1 + ‖Matrix.of h *ᵥ x‖) ^ (-(8 : ℝ)) = ((1 + ‖Matrix.of h *ᵥ x‖) ^ 8)⁻¹`. Rewrite using `[Real.rpow_neg (by positivity)]; norm_cast`. Rewrite using `[e8, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]`. Conclude with `key`.
-/
theorem Dbound (N : ℕ) (Ψ : M23 → ℂ) (B : ℝ)
    (hB : ∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n Ψ X‖ ≤ B)
    (h : M22) (n : ℕ) (hn : n ≤ N) (E0 : M23) (hE : ‖E0‖ ≤ 1) (x : Fin 2 → ℝ) :
    ‖iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)‖ ≤
      B / (1 + ‖h‖) ^ N * (1 + ‖Matrix.of h *ᵥ x‖) ^ (-(8 : ℝ)) := by
  obtain ⟨h1, h2⟩ := norm_le_Pm h x
  have hA : ‖iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)‖ ≤ ‖iteratedFDeriv ℝ n Ψ (Pm h x)‖ := by
    refine ((iteratedFDeriv ℝ n Ψ (Pm h x)).le_opNorm _).trans ?_
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hE)
  have hP : (1 + ‖h‖) ^ N * (1 + ‖Matrix.of h *ᵥ x‖) ^ 8 ≤ (1 + ‖Pm h x‖) ^ (N + 8) := by
    rw [pow_add]; gcongr
  have key : ‖iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)‖ *
      ((1 + ‖h‖) ^ N * (1 + ‖Matrix.of h *ᵥ x‖) ^ 8) ≤ B := by
    calc _ ≤ ‖iteratedFDeriv ℝ n Ψ (Pm h x)‖ * (1 + ‖Pm h x‖) ^ (N + 8) :=
          mul_le_mul hA hP (by positivity) (norm_nonneg _)
      _ ≤ B := by rw [mul_comm]; exact hB n hn _
  have e8 : (1 + ‖Matrix.of h *ᵥ x‖) ^ (-(8 : ℝ)) = ((1 + ‖Matrix.of h *ᵥ x‖) ^ 8)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]; norm_cast
  rw [e8, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
  exact key

/- English proof (translation)
Establish `hA : Differentiable ℝ (iteratedFDeriv ℝ k Ψ)` using `hΨ.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k)`. Conclude with `(hA.continuousMultilinear_apply_const _).comp fun x => (hasFDerivAt_Pm h x).differentiableAt`.
-/
theorem Ddiff (Ψ : M23 → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (h : M22) (E0 : M23) (k : ℕ) :
    Differentiable ℝ (fun x => iteratedFDeriv ℝ k Ψ (Pm h x) (fun _ => E0)) := by
  have hA : Differentiable ℝ (iteratedFDeriv ℝ k Ψ) :=
    hΨ.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k)
  exact (hA.continuousMultilinear_apply_const _).comp fun x => (hasFDerivAt_Pm h x).differentiableAt

/- English proof (translation)
Take `⟨hwi, hwe⟩` from `cov h hdet`. Establish `hc` using `(Ddiff Ψ hΨ h E0 n).continuous`. Establish `hF : Integrable (fun x => iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0))` using `(hwi.const_mul (B / (1 + ‖h‖) ^ N)).mono' hc.aestronglyMeasurable (ae_of_all _ (Dbound N Ψ B hB h n hn E0 hE))`. Use `⟨hF, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Dint (N : ℕ) (Ψ : M23 → ℂ) (B : ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hB : ∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n Ψ X‖ ≤ B)
    (h : M22) (hdet : (Matrix.of h).det ≠ 0) (n : ℕ) (hn : n ≤ N) (E0 : M23) (hE : ‖E0‖ ≤ 1) :
    Integrable (fun x => iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)) ∧
    ∫ x, ‖iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)‖ ≤
      B / (1 + ‖h‖) ^ N * (|(Matrix.of h).det|⁻¹ * ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(8 : ℝ))) := by
  obtain ⟨hwi, hwe⟩ := cov h hdet
  have hc := (Ddiff Ψ hΨ h E0 n).continuous
  have hF : Integrable (fun x => iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)) :=
    (hwi.const_mul (B / (1 + ‖h‖) ^ N)).mono' hc.aestronglyMeasurable
      (ae_of_all _ (Dbound N Ψ B hB h n hn E0 hE))
  refine ⟨hF, ?_⟩
  calc ∫ x, ‖iteratedFDeriv ℝ n Ψ (Pm h x) (fun _ => E0)‖
      ≤ ∫ x, B / (1 + ‖h‖) ^ N * (1 + ‖Matrix.of h *ᵥ x‖) ^ (-(8 : ℝ)) :=
        integral_mono hF.norm (hwi.const_mul _) (Dbound N Ψ B hB h n hn E0 hE)
    _ = _ := by rw [integral_const_mul, hwe]

/- English proof (translation)
Use `⟨(2 * Real.pi * Complex.I * β : ℂ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)), fun x => ?_, fun v => ?_, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [psiR, _root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Simplify using `[Complex.norm_exp]`.
-/
theorem phase (β : ℝ) : ∃ T : (Fin 2 → ℝ) →L[ℝ] ℂ, (∀ x, psiR (-(β * x 1)) = Complex.exp (T x)) ∧
    (∀ v, T v = 2 * Real.pi * Complex.I * β * (v 1 : ℂ)) ∧ ∀ x, ‖Complex.exp (T x)‖ = 1 := by
  refine ⟨(2 * Real.pi * Complex.I * β : ℂ) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)),
    fun x => ?_, fun v => ?_, fun x => ?_⟩
  · simp only [psiR, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    congr 1; push_cast; ring
  · simp
  · simp [Complex.norm_exp]

/- English proof (translation)
Take `⟨T, hT, hTv, hTn⟩` from `phase β`. Use `set v : Fin 2 → ℝ := (Matrix.of h)⁻¹ *ᵥ Pi.single i 1 with hvdef`. Establish `hMv : Matrix.of h *ᵥ v = Pi.single i 1`. Rewrite using `[hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]`. Establish `hv1 : v 1 = eta h i`.

Simplify using `[hvdef, eta]`. Establish `hE : ‖Lh h v‖ ≤ 1`. Use `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_` and prove the remaining obligations. Use `show ‖(if j = 2 then (Matrix.of h *ᵥ v) a else 0)‖ ≤ 1`. Rewrite using `[hMv]`.

Apply the tactic sequence `by_cases hj : j = 2 <;> by_cases ha : a = i <;> simp [hj, ha]`. Establish `hDv : ∀ k x, fderiv ℝ (fun x => iteratedFDeriv ℝ k Ψ (Pm h x) (fun _ => Lh h v)) x v = iteratedFDeriv ℝ (k + 1) Ψ (Pm h x) (fun _ => Lh h v)`. Introduce `k x`. Establish `hA : DifferentiableAt ℝ (iteratedFDeriv ℝ k Ψ) (Pm h x)` using `hΨ.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k) _`. Establish `hc : (fun x => iteratedFDeriv ℝ k Ψ (Pm h x) (fun _ => Lh h v)) = (fun X => iteratedFDeriv ℝ k Ψ X (fun _ => Lh h v)) ∘ Pm h` using `rfl`.

Rewrite using `[hc, fderiv_comp x (hA.continuousMultilinear_apply_const _) (hasFDerivAt_Pm h x).differentiableAt, ContinuousLinearMap.comp_apply, (hasFDerivAt_Pm h x).fderiv, fderiv_continuousMultilinear_apply_const_apply hA, iteratedFDeriv_succ_apply_left]`. Both sides reduce to the same expression. Establish `hχv : ∀ x, fderiv ℝ (fun x => Complex.exp (T x)) x v = T v * Complex.exp (T x)`. Introduce `x`. Rewrite using `[(T.hasFDerivAt.cexp).fderiv]`.

Simplify using `[smul_eq_mul, mul_comm]`. Establish `key` using `ibp_norm (fun k x => iteratedFDeriv ℝ k Ψ (Pm h x) (fun _ => Lh h v)) (fun x => Complex.exp (T x)) v (T v) (fun k => Ddiff Ψ hΨ h _ k) hDv T.differentiable.cexp hχv hTn n (fun k hk => (Dint N Ψ B hΨ hB h hdet k (hk.trans hn) _ hE).1)`. Establish `e0 : ∫ x, iteratedFDeriv ℝ 0 Ψ (Pm h x) (fun _ => Lh h v) * Complex.exp (T x) = innB Ψ h β`. Unfold `innB`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[iteratedFDeriv_zero_apply, hT]`. Both sides reduce to the same expression. Establish `enorm : ‖T v‖ = 2 * Real.pi * |β| * |eta h i|`. Rewrite using `[hTv, hv1]`.

Simplify using `[abs_of_pos Real.pi_pos]`. Rewrite `key` using `[e0, enorm]`. Conclude with `key.trans (Dint N Ψ B hΨ hB h hdet n hn _ hE).2`.
-/
theorem dir_bound (N : ℕ) (Ψ : M23 → ℂ) (B : ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hB : ∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n Ψ X‖ ≤ B)
    (h : M22) (hdet : (Matrix.of h).det ≠ 0) (β : ℝ) (i : Fin 2) (n : ℕ) (hn : n ≤ N) :
    (2 * Real.pi * |β| * |eta h i|) ^ n * ‖innB Ψ h β‖ ≤
      B / (1 + ‖h‖) ^ N * (|(Matrix.of h).det|⁻¹ * ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(8 : ℝ))) := by
  obtain ⟨T, hT, hTv, hTn⟩ := phase β
  set v : Fin 2 → ℝ := (Matrix.of h)⁻¹ *ᵥ Pi.single i 1 with hvdef
  have hMv : Matrix.of h *ᵥ v = Pi.single i 1 := by
    rw [hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have hv1 : v 1 = eta h i := by
    simp [hvdef, eta]
  have hE : ‖Lh h v‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    show ‖(if j = 2 then (Matrix.of h *ᵥ v) a else 0)‖ ≤ 1
    rw [hMv]
    by_cases hj : j = 2 <;> by_cases ha : a = i <;> simp [hj, ha]
  have hDv : ∀ k x, fderiv ℝ (fun x => iteratedFDeriv ℝ k Ψ (Pm h x) (fun _ => Lh h v)) x v =
      iteratedFDeriv ℝ (k + 1) Ψ (Pm h x) (fun _ => Lh h v) := by
    intro k x
    have hA : DifferentiableAt ℝ (iteratedFDeriv ℝ k Ψ) (Pm h x) :=
      hΨ.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k) _
    have hc : (fun x => iteratedFDeriv ℝ k Ψ (Pm h x) (fun _ => Lh h v)) =
        (fun X => iteratedFDeriv ℝ k Ψ X (fun _ => Lh h v)) ∘ Pm h := rfl
    rw [hc, fderiv_comp x (hA.continuousMultilinear_apply_const _) (hasFDerivAt_Pm h x).differentiableAt,
      ContinuousLinearMap.comp_apply, (hasFDerivAt_Pm h x).fderiv,
      fderiv_continuousMultilinear_apply_const_apply hA, iteratedFDeriv_succ_apply_left]
    rfl
  have hχv : ∀ x, fderiv ℝ (fun x => Complex.exp (T x)) x v = T v * Complex.exp (T x) := by
    intro x
    rw [(T.hasFDerivAt.cexp).fderiv]
    simp [smul_eq_mul, mul_comm]
  have key := ibp_norm (fun k x => iteratedFDeriv ℝ k Ψ (Pm h x) (fun _ => Lh h v))
    (fun x => Complex.exp (T x)) v (T v) (fun k => Ddiff Ψ hΨ h _ k) hDv T.differentiable.cexp hχv
    hTn n (fun k hk => (Dint N Ψ B hΨ hB h hdet k (hk.trans hn) _ hE).1)
  have e0 : ∫ x, iteratedFDeriv ℝ 0 Ψ (Pm h x) (fun _ => Lh h v) * Complex.exp (T x) = innB Ψ h β := by
    unfold innB; congr 1; funext x; rw [iteratedFDeriv_zero_apply, hT]; rfl
  have enorm : ‖T v‖ = 2 * Real.pi * |β| * |eta h i| := by
    rw [hTv, hv1]; simp [abs_of_pos Real.pi_pos]
  rw [e0, enorm] at key
  exact key.trans (Dint N Ψ B hΨ hB h hdet n hn _ hE).2

end Ibp

open Ibp in
/- English proof (translation)
Introduce `N`. Use `⟨2 ^ (N + 1) * ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(8 : ℝ)), ?_⟩` and prove the remaining obligations. Introduce `Ψ B hΨ hB h β hdet`. Use `set I0 := ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(8 : ℝ)) with hI0`. Use `set K := B / (1 + ‖h‖) ^ N * (|(Matrix.of h).det|⁻¹ * I0) with hK`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ‖eta h‖ ≤ |eta h i| := by`. Break down `le_total |eta h 0| |eta h 1| with hle | hle` into its components or cases. Use `⟨1, (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_⟩ fin_cases j` and prove the remaining obligations. Simplify using `using hle`. Simplify using the standard rewrite rules.

Use `⟨0, (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_⟩ fin_cases j` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `using hle`. Use `set t := |β| * ‖eta h‖ with ht_def`. Establish `ht : 0 ≤ t` using `by positivity`.

Establish `h0` using `dir_bound N Ψ B hΨ hB h hdet β i 0 (Nat.zero_le _)`. Establish `hN` using `dir_bound N Ψ B hΨ hB h hdet β i N le_rfl`. Rewrite `h0` using `[pow_zero, one_mul]`. Establish `htle : t ≤ 2 * Real.pi * |β| * |eta h i|`. Establish `h1 : t ≤ |β| * |eta h i|` using `mul_le_mul_of_nonneg_left hi (abs_nonneg _)`.

Establish `h2 : (1 : ℝ) ≤ 2 * Real.pi` using `by linarith [Real.pi_gt_three]`. Use polynomial arithmetic with `[abs_nonneg β, abs_nonneg (eta h i), mul_nonneg (abs_nonneg β) (abs_nonneg (eta h i))]`. Establish `htN : t ^ N * ‖innB Ψ h β‖ ≤ K` using `(mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht htle N) (norm_nonneg _)).trans hN`. Establish `hpow : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N)`. Break down `le_total t 1 with h1 | h1` into its components or cases.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hinner : ‖innB Ψ h β‖ * (1 + t) ^ N ≤ 2 ^ N * (2 * K)`. Combine the equalities or inequalities in the displayed calculation. Establish `hp : (0 : ℝ) < (1 + ‖h‖) ^ N` using `by positivity`.

Rewrite using `[le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hK]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ibpBound : IbpBound := by
  intro N
  refine ⟨2 ^ (N + 1) * ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(8 : ℝ)), ?_⟩
  intro Ψ B hΨ hB h β hdet
  set I0 := ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(8 : ℝ)) with hI0
  set K := B / (1 + ‖h‖) ^ N * (|(Matrix.of h).det|⁻¹ * I0) with hK
  obtain ⟨i, hi⟩ : ∃ i, ‖eta h‖ ≤ |eta h i| := by
    rcases le_total |eta h 0| |eta h 1| with hle | hle
    · refine ⟨1, (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_⟩
      fin_cases j
      · simpa using hle
      · simp
    · refine ⟨0, (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_⟩
      fin_cases j
      · simp
      · simpa using hle
  set t := |β| * ‖eta h‖ with ht_def
  have ht : 0 ≤ t := by positivity
  have h0 := dir_bound N Ψ B hΨ hB h hdet β i 0 (Nat.zero_le _)
  have hN := dir_bound N Ψ B hΨ hB h hdet β i N le_rfl
  rw [pow_zero, one_mul] at h0
  have htle : t ≤ 2 * Real.pi * |β| * |eta h i| := by
    have h1 : t ≤ |β| * |eta h i| := mul_le_mul_of_nonneg_left hi (abs_nonneg _)
    have h2 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [abs_nonneg β, abs_nonneg (eta h i), mul_nonneg (abs_nonneg β) (abs_nonneg (eta h i))]
  have htN : t ^ N * ‖innB Ψ h β‖ ≤ K :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht htle N) (norm_nonneg _)).trans hN
  have hpow : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
    rcases le_total t 1 with h1 | h1
    · calc (1 + t) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ ≤ 2 ^ N * (1 + t ^ N) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ht N])
    · calc (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * t ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (1 + t ^ N) := by gcongr; linarith
  have hinner : ‖innB Ψ h β‖ * (1 + t) ^ N ≤ 2 ^ N * (2 * K) := by
    calc ‖innB Ψ h β‖ * (1 + t) ^ N ≤ ‖innB Ψ h β‖ * (2 ^ N * (1 + t ^ N)) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = 2 ^ N * (‖innB Ψ h β‖ + t ^ N * ‖innB Ψ h β‖) := by ring
      _ ≤ 2 ^ N * (K + K) := by gcongr
      _ = 2 ^ N * (2 * K) := by ring
  have hp : (0 : ℝ) < (1 + ‖h‖) ^ N := by positivity
  rw [le_div_iff₀ (by positivity)]
  calc ‖innB Ψ h β‖ * ((1 + ‖h‖) ^ N * (1 + t) ^ N)
      = (1 + ‖h‖) ^ N * (‖innB Ψ h β‖ * (1 + t) ^ N) := by ring
    _ ≤ (1 + ‖h‖) ^ N * (2 ^ N * (2 * K)) := mul_le_mul_of_nonneg_left hinner hp.le
    _ = 2 ^ (N + 1) * I0 * B * |(Matrix.of h).det|⁻¹ := by
      rw [hK]; field_simp; ring

end Ad3.LR.B
