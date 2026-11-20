import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.UnfoldZn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofTorMkCIsQuotientMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.NormSqRiemannThetaMulExpPeriodic

open Complex Matrix MeasureTheory
open scoped Real MatrixOrder

noncomputable section

namespace GlobalTheory.ThetaNorm

/- English proof (translation)
Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg`. Establish `hBt : Y = Bᵀ * B` using `by rw [hB]; rfl`. Establish `hdet : Y.det = B.det ^ 2` using `by rw [hBt, det_mul, det_transpose, sq]`. Establish `hB0 : B.det ≠ 0`. Introduce `h`.

Use `hY.det_pos` as an intermediate fact. Rewrite `this` using `[hdet, h]`. Simplify using `at this`. Use `set M := Matrix.toLin' B with hM`. Establish `hMdet : LinearMap.det M ≠ 0` using `by rw [hM, LinearMap.det_toLin']; exact hB0`.

Use `set F : (Fin g → ℝ) → ℝ := fun w => ∏ i, Real.exp (-(2 * π) * w i ^ 2) with hF`. Establish `hFc : Continuous F` using `by rw [hF]; fun_prop`. Establish `h1 (y : Fin g → ℝ) : Real.exp (-2 * π * (y ⬝ᵥ Y *ᵥ y)) = F (M y)`. Rewrite using `[hBt, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hF]`. Simplify using `only [← Real.exp_sum, hM, toLin'_apply, dotProduct, Finset.mul_sum]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Simplify using `only [h1]`. Establish `hFm : Measurable fun w => ENNReal.ofReal (F w)` using `ENNReal.measurable_ofReal.comp hFc.measurable`. Establish `hMm : Measurable M` using `(LinearMap.continuous_of_finiteDimensional M).measurable`.

Establish `hint : Integrable F`. Rewrite using `[hF, volume_pi]`. Conclude with `Integrable.fintype_prod (f := fun _ (t : ℝ) => Real.exp (-(2 * π) * t ^ 2)) fun _ => integrable_exp_neg_mul_sq (by positivity)`. Establish `hval : ∫ w, F w = (Real.sqrt 2)⁻¹ ^ g`. Rewrite using `[hF, integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-(2 * π) * t ^ 2)), integral_gaussian, Fintype.card_fin, ← Real.sqrt_inv]`.

Use `congr 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← lintegral_map hFm hMm, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hMdet, lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le), hval, smul_eq_mul, ← ENNReal.ofReal_m …`. Use `congr 3`. Rewrite using `[eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow, Real.mul_self_sqrt (by norm_num)]`.
-/
theorem lintegral_exp_neg_quadratic {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) :
    ∫⁻ y : Fin g → ℝ, ENNReal.ofReal (Real.exp (-2 * π * (y ⬝ᵥ Y *ᵥ y))) =
      ENNReal.ofReal (Real.sqrt (2 ^ g * Y.det))⁻¹ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hBt : Y = Bᵀ * B := by rw [hB]; rfl
  have hdet : Y.det = B.det ^ 2 := by rw [hBt, det_mul, det_transpose, sq]
  have hB0 : B.det ≠ 0 := by
    intro h
    have := hY.det_pos
    rw [hdet, h] at this
    simp at this
  set M := Matrix.toLin' B with hM
  have hMdet : LinearMap.det M ≠ 0 := by rw [hM, LinearMap.det_toLin']; exact hB0
  set F : (Fin g → ℝ) → ℝ := fun w => ∏ i, Real.exp (-(2 * π) * w i ^ 2) with hF
  have hFc : Continuous F := by rw [hF]; fun_prop
  have h1 (y : Fin g → ℝ) : Real.exp (-2 * π * (y ⬝ᵥ Y *ᵥ y)) = F (M y) := by
    rw [hBt, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hF]
    simp only [← Real.exp_sum, hM, toLin'_apply, dotProduct, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h1]
  have hFm : Measurable fun w => ENNReal.ofReal (F w) :=
    ENNReal.measurable_ofReal.comp hFc.measurable
  have hMm : Measurable M := (LinearMap.continuous_of_finiteDimensional M).measurable
  have hint : Integrable F := by
    rw [hF, volume_pi]
    exact Integrable.fintype_prod (f := fun _ (t : ℝ) => Real.exp (-(2 * π) * t ^ 2))
      fun _ => integrable_exp_neg_mul_sq (by positivity)
  have hval : ∫ w, F w = (Real.sqrt 2)⁻¹ ^ g := by
    rw [hF, integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-(2 * π) * t ^ 2)),
      integral_gaussian, Fintype.card_fin, ← Real.sqrt_inv]
    congr 2
    field_simp
  rw [← lintegral_map hFm hMm, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hMdet,
    lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun w => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le),
    hval, smul_eq_mul, ← ENNReal.ofReal_mul (abs_nonneg _), hM, LinearMap.det_toLin', hdet,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_inv, mul_inv, mul_comm, inv_pow]
  congr 3
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
    Real.mul_self_sqrt (by norm_num)]

/- English proof (translation)
Establish `hn (m : Fin g → ℤ) (x : Fin g → ℝ) : ‖c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ)))‖ = ‖c m‖`. Rewrite using `[norm_mul, Complex.norm_exp]`. Simplify using `[dotProduct]`. Establish `hbox : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =ᵐ[volume] Set.Icc 0 1`. Establish `e : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} = Set.univ.pi fun i => Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i)` using `by ext; simp`.

Rewrite using `[e]`. Conclude with `Measure.univ_pi_Ioc_ae_eq_Icc`. Establish `h` using `ReciprocityTheory.ChartRestriction.G.I2.tof_torus_parseval (fun x : Fin g → ℝ => ∑' m, c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ)))) (continuous_tsum (fun m => by simp only [dotProduct]; fun_prop) hc fun m x => (hn m x).le) (fun x n => tsum_congr fun m => …`. Use `congr 1`. Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`.

Use `⟨m ⬝ᵥ n, ?_⟩` and prove the remaining obligations. Simplify using `only [dotProduct, Pi.add_apply]`. Use `push_cast`. Simplify using `only [mul_add, Finset.sum_add_distrib]`. Use the proof step `ring)`.

Simplify using `only [setIntegral_congr_set hbox] at h`. Use `h using 3 with n` and compare the differences between its conclusion and the goal. Rewrite using `[← integral_Icc_tsum_mul_cexp hc n]`. Use `congr 2`. Use function extensionality and compare the values at `x`.

Rewrite using `[mul_comm, neg_mul]`. Both sides reduce to the same expression.
-/
theorem hasSum_norm_sq_of_summable {g : ℕ} {c : (Fin g → ℤ) → ℂ} (hc : Summable fun m => ‖c m‖) :
    HasSum (fun m => ‖c m‖ ^ 2) (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      ‖∑' m, c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ)))‖ ^ 2) := by
  have hn (m : Fin g → ℤ) (x : Fin g → ℝ) :
      ‖c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ)))‖ = ‖c m‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp [dotProduct]
  have hbox : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =ᵐ[volume] Set.Icc 0 1 := by
    have e : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.univ.pi fun i => Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i) := by
      ext; simp
    rw [e]
    exact Measure.univ_pi_Ioc_ae_eq_Icc
  have h := ReciprocityTheory.ChartRestriction.G.I2.tof_torus_parseval
    (fun x : Fin g → ℝ =>
      ∑' m, c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))))
    (continuous_tsum (fun m => by simp only [dotProduct]; fun_prop) hc fun m x => (hn m x).le)
    (fun x n => tsum_congr fun m => by
      congr 1
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨m ⬝ᵥ n, ?_⟩
      simp only [dotProduct, Pi.add_apply]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      ring)
  simp only [setIntegral_congr_set hbox] at h
  convert h using 3 with n
  rw [← integral_Icc_tsum_mul_cexp hc n]
  congr 2
  funext x
  rw [mul_comm, neg_mul]
  rfl

/- English proof (translation)
Use `hasSum_norm_sq_of_summable (h.summable_norm_riemannThetaTerm a b v) using 4 with x` and compare the differences between its conclusion and the goal. Rewrite using `[riemannTheta_add_ofReal_eq_tsum, norm_mul, Complex.norm_exp]`. Simplify using `[dotProduct]`.
-/
theorem hasSum_integral_norm_sq_riemannTheta {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (h : IsSiegel τ) (a b : Fin g → ℝ) (v : Fin g → ℂ) :
    HasSum (fun m => ‖riemannThetaTerm a b τ v m‖ ^ 2) (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      ‖riemannTheta a b τ (v + fun i => (x i : ℂ))‖ ^ 2) := by
  convert hasSum_norm_sq_of_summable (h.summable_norm_riemannThetaTerm a b v) using 4 with x
  rw [riemannTheta_add_ofReal_eq_tsum, norm_mul, Complex.norm_exp]
  simp [dotProduct]

/- English proof (translation)
Establish `hs : (τ.map Complex.im).IsSymm` using `h.map _`. Establish `e1 : (fun i => ((τ *ᵥ fun i => (y i : ℂ)) i).im) = τ.map Complex.im *ᵥ y`. Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct]`. Establish `e2 : y + (fun i => (n i : ℝ)) + a = y + fun i => (n i : ℝ) + a i`.

Rewrite using `[add_assoc]`. Both sides reduce to the same expression. Rewrite using `[norm_riemannThetaTerm, e1, e2, ← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 1`. Generalize the expression as in `(fun i => (n i : ℝ) + a i) = u`.

Establish `e3 : y ⬝ᵥ τ.map Complex.im *ᵥ u = u ⬝ᵥ τ.map Complex.im *ᵥ y`. Rewrite using `[dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]`. Rewrite using `[mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, e3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_riemannThetaTerm_mul_exp {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (h : τ.IsSymm) (a b y : Fin g → ℝ) (n : Fin g → ℤ) :
    ‖riemannThetaTerm a b τ (τ *ᵥ fun i => (y i : ℂ)) n‖ ^ 2 *
        Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y)) =
      Real.exp (-2 * π * ((y + (fun i => (n i : ℝ)) + a) ⬝ᵥ
        τ.map Complex.im *ᵥ (y + (fun i => (n i : ℝ)) + a))) := by
  have hs : (τ.map Complex.im).IsSymm := h.map _
  have e1 : (fun i => ((τ *ᵥ fun i => (y i : ℂ)) i).im) = τ.map Complex.im *ᵥ y := by
    funext i
    simp [mulVec, dotProduct]
  have e2 : y + (fun i => (n i : ℝ)) + a = y + fun i => (n i : ℝ) + a i := by
    rw [add_assoc]; rfl
  rw [norm_riemannThetaTerm, e1, e2, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  generalize (fun i => (n i : ℝ) + a i) = u
  have e3 : y ⬝ᵥ τ.map Complex.im *ᵥ u = u ⬝ᵥ τ.map Complex.im *ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, e3]
  push_cast
  ring

/- English proof (translation)
Establish `hθ : Continuous (riemannTheta a b τ)` using `(continuousOn_riemannTheta a b).comp_continuous (f := fun v => (v, τ)) (by fun_prop) fun v => ⟨trivial, h⟩`. Establish `hbox : (Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1) =ᵐ[volume] Set.Icc 0 1` using `Measure.univ_pi_Ico_ae_eq_Icc (f := (0 : Fin g → ℝ)) (g := 1)`. Use `set G : (Fin g → ℝ) → ENNReal := fun y => ENNReal.ofReal (Real.exp (-2 * π * ((y + a) ⬝ᵥ τ.map Complex.im *ᵥ (y + a)))) with hG`. Establish `hGm : Measurable G`. Use `ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)` and prove the remaining obligations.

Simplify using `only [dotProduct, mulVec]`. Use `fun_prop`. Establish `hin (y : Fin g → ℝ) : ∫⁻ x in Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1, ENNReal.ofReal (‖riemannTheta a b τ ((fun i => (x i : ℂ)) + τ *ᵥ fun i => (y i : ℂ))‖ ^ 2 * Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y))) = ∑' n : Fin g → ℤ, G (y + fun i => (n i : ℝ))`. Establish `hs` using `(hasSum_integral_norm_sq_riemannTheta h a b (τ *ᵥ fun i => (y i : ℂ))).mul_right (Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y)))`. Simplify using `only [norm_sq_riemannThetaTerm_mul_exp h.isSymm] at hs`.

Rewrite using `[setLIntegral_congr hbox, ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop)) (Filter.Eventually.of_forall fun x => by positivity), integral_mul_const]`. Simplify using `only [add_comm _ (τ *ᵥ _)]`. Rewrite using `[← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hs.summable]`. Simplify using `only [hin]`. Establish `hc : ReciprocityTheory.ChartRestriction.G.I2.cubeIco (Fin g) = Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1` using `by ext; simp [ReciprocityTheory.ChartRestriction.G.I2.cubeIco]`.

Rewrite using `[lintegral_tsum (f := fun (n : Fin g → ℤ) y => G (y + fun i => (n i : ℝ))) fun n => (hGm.comp (measurable_add_const _)).aemeasurable, ← hc, ← ReciprocityTheory.ChartRestriction.G.I2.unfold_Zn G, ← lintegral_exp_neg_quadratic h.posDef]`. Conclude with `lintegral_add_right_eq_self (fun y => ENNReal.ofReal (Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y)))) a`.
-/
theorem lintegral_lintegral_norm_sq_riemannTheta {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (h : IsSiegel τ) (a b : Fin g → ℝ) :
    ∫⁻ y in Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1,
      ∫⁻ x in Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1, ENNReal.ofReal
        (‖riemannTheta a b τ ((fun i => (x i : ℂ)) + τ *ᵥ fun i => (y i : ℂ))‖ ^ 2 *
          Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y))) =
      ENNReal.ofReal (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  have hθ : Continuous (riemannTheta a b τ) :=
    (continuousOn_riemannTheta a b).comp_continuous (f := fun v => (v, τ)) (by fun_prop)
      fun v => ⟨trivial, h⟩
  have hbox : (Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1) =ᵐ[volume] Set.Icc 0 1 :=
    Measure.univ_pi_Ico_ae_eq_Icc (f := (0 : Fin g → ℝ)) (g := 1)
  set G : (Fin g → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal (Real.exp (-2 * π * ((y + a) ⬝ᵥ τ.map Complex.im *ᵥ (y + a)))) with hG
  have hGm : Measurable G := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    simp only [dotProduct, mulVec]
    fun_prop
  have hin (y : Fin g → ℝ) :
      ∫⁻ x in Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1, ENNReal.ofReal
        (‖riemannTheta a b τ ((fun i => (x i : ℂ)) + τ *ᵥ fun i => (y i : ℂ))‖ ^ 2 *
          Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y))) =
      ∑' n : Fin g → ℤ, G (y + fun i => (n i : ℝ)) := by
    have hs := (hasSum_integral_norm_sq_riemannTheta h a b (τ *ᵥ fun i => (y i : ℂ))).mul_right
      (Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y)))
    simp only [norm_sq_riemannThetaTerm_mul_exp h.isSymm] at hs
    rw [setLIntegral_congr hbox, ← ofReal_integral_eq_lintegral_ofReal
      (Continuous.integrableOn_Icc (by fun_prop))
      (Filter.Eventually.of_forall fun x => by positivity), integral_mul_const]
    simp only [add_comm _ (τ *ᵥ _)]
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hs.summable]
  simp only [hin]
  have hc : ReciprocityTheory.ChartRestriction.G.I2.cubeIco (Fin g) = Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1 := by
    ext; simp [ReciprocityTheory.ChartRestriction.G.I2.cubeIco]
  rw [lintegral_tsum (f := fun (n : Fin g → ℤ) y => G (y + fun i => (n i : ℝ)))
      fun n => (hGm.comp (measurable_add_const _)).aemeasurable, ← hc,
    ← ReciprocityTheory.ChartRestriction.G.I2.unfold_Zn G, ← lintegral_exp_neg_quadratic h.posDef]
  exact lintegral_add_right_eq_self
    (fun y => ENNReal.ofReal (Real.exp (-2 * π * (y ⬝ᵥ τ.map Complex.im *ᵥ y)))) a

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

/- English proof (translation)
Introduce `g τ a b hs hp`. Establish `h : IsSiegel τ` using `⟨hs, hp⟩`. Establish `hθ : Continuous (riemannTheta a b τ)` using `(continuousOn_riemannTheta a b).comp_continuous (f := fun v => (v, τ)) (by fun_prop) fun v => ⟨trivial, h⟩`. Simplify using `only [← RiemannThetaModel.riemannTheta_eq_thetaChar]`. Use `set f : (Fin g → ℝ) × (Fin g → ℝ) → ℝ := fun q => ‖riemannTheta a b τ ((fun i => (q.1 i : ℂ)) + τ *ᵥ fun i => (q.2 i : ℂ))‖ ^ 2 * Real.exp (-2 * π * (q.2 ⬝ᵥ τ.map Complex.im *ᵥ q.2)) with hf`.

Establish `hfc : Continuous f`. Use `Continuous.mul (((hθ.comp ?_).norm).pow 2) ?_` and prove the remaining obligations. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, dotProduct, mulVec]`. Use `fun_prop`.

Simplify using `only [dotProduct, mulVec] fun_prop`. Establish `hmp` using `volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin g ⊕ Fin g => ℝ)`. Use `set C := Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1 with hC`. Establish `hpre : Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1) = MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin g ⊕ Fin g => ℝ) ⁻¹' (C ×ˢ C)`. Use extensionality with `p`.

Simplify using `[hC, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi]`. Establish `key` using `hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) f (C ×ˢ C)`. Rewrite using `[hpre]`. Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => by`.

Simplify using `only [hf]`. Use the proof step `positivity) hfc.aestronglyMeasurable, Measure.volume_eq_prod,`. Use the proof step `← Measure.prod_restrict, lintegral_prod_symm' (fun q => ENNReal.ofReal (f q)) (ENNReal.measurable_ofReal.comp hfc.measurable)]`. Simplify using `only [hf, hC]`. Rewrite using `[lintegral_lintegral_norm_sq_riemannTheta h, ENNReal.toReal_ofReal (by positivity)]`.
-/
theorem integral_norm_sq_thetaChar :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ), τ.IsSymm →
      (τ.map Complex.im).PosDef →
      ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
        ‖thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ))
            ((fun i => (p (.inl i) : ℂ)) + τ.mulVec (fun i => (p (.inr i) : ℂ)))‖ ^ 2 *
          Real.exp (-2 * Real.pi *
            ((fun i => p (.inr i)) ⬝ᵥ (τ.map Complex.im).mulVec (fun i => p (.inr i)))) =
        (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ a b hs hp
  have h : IsSiegel τ := ⟨hs, hp⟩
  have hθ : Continuous (riemannTheta a b τ) :=
    (continuousOn_riemannTheta a b).comp_continuous (f := fun v => (v, τ)) (by fun_prop)
      fun v => ⟨trivial, h⟩
  simp only [← RiemannThetaModel.riemannTheta_eq_thetaChar]
  set f : (Fin g → ℝ) × (Fin g → ℝ) → ℝ := fun q =>
    ‖riemannTheta a b τ ((fun i => (q.1 i : ℂ)) + τ *ᵥ fun i => (q.2 i : ℂ))‖ ^ 2 *
      Real.exp (-2 * π * (q.2 ⬝ᵥ τ.map Complex.im *ᵥ q.2)) with hf
  have hfc : Continuous f := by
    refine Continuous.mul (((hθ.comp ?_).norm).pow 2) ?_
    · refine continuous_pi fun i => ?_
      simp only [Pi.add_apply, dotProduct, mulVec]
      fun_prop
    · simp only [dotProduct, mulVec]
      fun_prop
  have hmp := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin g ⊕ Fin g => ℝ)
  set C := Set.univ.pi fun _ : Fin g => Set.Ico (0 : ℝ) 1 with hC
  have hpre : Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1) =
      MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin g ⊕ Fin g => ℝ) ⁻¹' (C ×ˢ C) := by
    ext p
    simp [hC, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  have key := hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) f (C ×ˢ C)
  rw [hpre]
  refine key.trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => by
      simp only [hf]; positivity) hfc.aestronglyMeasurable, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod_symm' (fun q => ENNReal.ofReal (f q))
      (ENNReal.measurable_ofReal.comp hfc.measurable)]
  simp only [hf, hC]
  rw [lintegral_lintegral_norm_sq_riemannTheta h, ENNReal.toReal_ofReal (by positivity)]

end GlobalTheory.ThetaNorm
