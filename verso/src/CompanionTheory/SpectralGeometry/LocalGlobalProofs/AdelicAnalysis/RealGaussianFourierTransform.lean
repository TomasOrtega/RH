import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SimultaneousNormalFormMajorant
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.GaussOne

noncomputable def beta (τ : ℂ) (e : ℝ) : ℂ :=
  (τ.im : ℂ) - Complex.I * (τ.re : ℂ) * (e : ℂ)

/- English proof (translation)
Simplify using `[beta]`.
-/
lemma beta_re (τ : ℂ) {e : ℝ} : (beta τ e).re = τ.im := by
  simp [beta]

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [beta]`.
-/
lemma beta_one (τ : ℂ) : beta τ 1 = -Complex.I * τ := by
  apply Complex.ext <;> simp [beta]

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp [beta]`.
-/
lemma beta_neg_one (τ : ℂ) : beta τ (-1) = Complex.I * (starRingEnd ℂ) τ := by
  apply Complex.ext <;> simp [beta]

/- English proof (translation)
Establish `hc : (starRingEnd ℂ) τ ≠ 0` using `by simpa using hτ`. Break down `he with rfl | rfl` into its components or cases. Rewrite using `[beta_one, beta_one]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts.

Simplify using the standard rewrite rules. Rewrite using `[beta_neg_one, beta_neg_one]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Simplify using `only [map_neg, map_inv₀]`. Clear the denominators using the available nonvanishing facts.

Simplify using the standard rewrite rules.
-/
lemma beta_inv {τ : ℂ} (hτ : τ ≠ 0) {e : ℝ} (he : e = 1 ∨ e = -1) :
    beta (-τ⁻¹) e = (beta τ e)⁻¹ := by
  have hc : (starRingEnd ℂ) τ ≠ 0 := by simpa using hτ
  rcases he with rfl | rfl
  · rw [beta_one, beta_one]
    apply eq_inv_of_mul_eq_one_left
    field_simp
    simp
  · rw [beta_neg_one, beta_neg_one]
    apply eq_inv_of_mul_eq_one_left
    simp only [map_neg, map_inv₀]
    field_simp
    simp

/- English proof (translation)
Break down `he with rfl | rfl` into its components or cases. Rewrite using `[beta_one]`. Simplify using the standard rewrite rules. Rewrite using `[beta_neg_one]`. Simplify using the standard rewrite rules.
-/
lemma norm_beta (τ : ℂ) {e : ℝ} (he : e = 1 ∨ e = -1) : ‖beta τ e‖ = ‖τ‖ := by
  rcases he with rfl | rfl
  · rw [beta_one]; simp
  · rw [beta_neg_one]; simp

/- English proof (translation)
Establish `h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[h, Complex.norm_cpow_real, norm_inv, norm_beta τ he, Real.inv_rpow (norm_nonneg _), Real.sqrt_eq_rpow]`.
-/
lemma norm_half (τ : ℂ) {e : ℝ} (he : e = 1 ∨ e = -1) :
    ‖((beta τ e)⁻¹) ^ (1 / 2 : ℂ)‖ = (Real.sqrt ‖τ‖)⁻¹ := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_cpow_real, norm_inv, norm_beta τ he, Real.inv_rpow (norm_nonneg _),
    Real.sqrt_eq_rpow]

/- English proof (translation)
Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hb`. Establish `harg : b.arg ≠ Real.pi`. Rewrite using `[Ne, Complex.arg_eq_pi_iff, not_and_or, not_lt]`.

Conclude with `Or.inl hb.le`. Rewrite using `[inv_inv, Complex.inv_cpow _ _ harg, inv_mul_cancel₀]`. Simplify using `[Complex.cpow_eq_zero_iff, hb0]`.
-/
lemma half_mul {b : ℂ} (hb : 0 < b.re) :
    (b⁻¹) ^ (1 / 2 : ℂ) * ((b⁻¹)⁻¹) ^ (1 / 2 : ℂ) = 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have harg : b.arg ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff, not_and_or, not_lt]
    exact Or.inl hb.le
  rw [inv_inv, Complex.inv_cpow _ _ harg, inv_mul_cancel₀]
  simp [Complex.cpow_eq_zero_iff, hb0]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hm` using `Real.map_matrix_volume_pi_eq_smul_volume_pi hg`. Establish `hc : Continuous (Matrix.toLin' g)` using `LinearMap.continuous_of_finiteDimensional _`. Establish `hc0 : ENNReal.ofReal |(g.det)⁻¹| ≠ 0`. Simplify `hg` using `[abs_pos]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h1 : Integrable F (Measure.map (Matrix.toLin' g) volume)` using `(integrable_map_measure hF.aestronglyMeasurable hc.aemeasurable).2 h`. Rewrite `h1` using `[hm]`. Conclude with `(integrable_smul_measure hc0 ENNReal.ofReal_ne_top).1 h1`. Establish `h1 : ∫ u, F (Matrix.toLin' g u) = ∫ x, F x ∂(Measure.map (Matrix.toLin' g) volume)` using `(integral_map hc.aemeasurable hF.aestronglyMeasurable).symm`.

Establish `h2 : ∫ u, F (g *ᵥ u) = ∫ u, F (Matrix.toLin' g u)` using `rfl`. Rewrite using `[h2, h1, hm, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, Complex.real_smul]`.
-/
lemma subst (g : Matrix ι ι ℝ) (hg : g.det ≠ 0) (F : (ι → ℝ) → ℂ) (hF : Continuous F) :
    (Integrable (fun u => F (g *ᵥ u)) → Integrable F) ∧
      ∫ u, F (g *ᵥ u) = ((|g.det|⁻¹ : ℝ) : ℂ) * ∫ x, F x := by
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hg
  have hc : Continuous (Matrix.toLin' g) := LinearMap.continuous_of_finiteDimensional _
  have hc0 : ENNReal.ofReal |(g.det)⁻¹| ≠ 0 := by
    simpa [abs_pos] using hg
  constructor
  · intro h
    have h1 : Integrable F (Measure.map (Matrix.toLin' g) volume) :=
      (integrable_map_measure hF.aestronglyMeasurable hc.aemeasurable).2 h
    rw [hm] at h1
    exact (integrable_smul_measure hc0 ENNReal.ofReal_ne_top).1 h1
  · have h1 : ∫ u, F (Matrix.toLin' g u) = ∫ x, F x ∂(Measure.map (Matrix.toLin' g) volume) :=
      (integral_map hc.aemeasurable hF.aestronglyMeasurable).symm
    have h2 : ∫ u, F (g *ᵥ u) = ∫ u, F (Matrix.toLin' g u) := rfl
    rw [h2, h1, hm, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
      Complex.real_smul]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u gᵀ, Matrix.vecMul_transpose]`.
-/
lemma bil (g A : Matrix ι ι ℝ) (u w : ι → ℝ) :
    (g *ᵥ u) ⬝ᵥ (A *ᵥ (g *ᵥ w)) = u ⬝ᵥ ((gᵀ * A * g) *ᵥ w) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u gᵀ,
    Matrix.vecMul_transpose]

/- English proof (translation)
Rewrite using `[bil, bil, hS, hP]`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Matrix.one_mulVec]`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [beta]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma quad {g S P : Matrix ι ι ℝ} {e : ι → ℝ} (hS : gᵀ * S * g = Matrix.diagonal e)
    (hP : gᵀ * P * g = 1) (τ : ℂ) (u : ι → ℝ) :
    (Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ u)) : ℝ) : ℂ)
        - (Real.pi : ℂ) * (τ.im : ℂ) * (((g *ᵥ u) ⬝ᵥ (P *ᵥ (g *ᵥ u)) : ℝ) : ℂ)
      = -∑ i, ((Real.pi : ℂ) * beta τ (e i)) * (u i : ℂ) ^ 2 := by
  rw [bil, bil, hS, hP]
  simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.one_mulVec]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [beta]
  ring

/- English proof (translation)
Rewrite using `[bil, hS]`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal]`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma lin {g S : Matrix ι ι ℝ} {e : ι → ℝ} (hS : gᵀ * S * g = Matrix.diagonal e)
    (u v : ι → ℝ) :
    2 * (Real.pi : ℂ) * Complex.I * (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ)
      = ∑ i, (2 * (Real.pi : ℂ) * Complex.I * (e i : ℂ) * (v i : ℂ)) * (u i : ℂ) := by
  rw [bil, hS]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Establish `h1 : g.det ^ 2 * S.det = ∏ i, e i`. Use `congrArg Matrix.det hS` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : |∏ i, e i| = 1`. Rewrite using `[Finset.abs_prod]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases he i with h | h <;> simp [h]`. Establish `h3 : |S.det| * |g.det| ^ 2 = 1`.

Rewrite using `[← h2, ← h1, abs_mul, abs_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : Real.sqrt (|S.det| * |g.det| ^ 2) = 1` using `by rw [h3]; simp`. Rewrite `h4` using `[Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq (abs_nonneg _)]`. Then use the resulting hypothesis.
-/
lemma det_scale {g S : Matrix ι ι ℝ} {e : ι → ℝ} (he : ∀ i, e i = 1 ∨ e i = -1)
    (hS : gᵀ * S * g = Matrix.diagonal e) : Real.sqrt |S.det| * |g.det| = 1 := by
  have h1 : g.det ^ 2 * S.det = ∏ i, e i := by
    have := congrArg Matrix.det hS
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    rw [← this]; ring
  have h2 : |∏ i, e i| = 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rcases he i with h | h <;> simp [h]
  have h3 : |S.det| * |g.det| ^ 2 = 1 := by
    rw [← h2, ← h1, abs_mul, abs_pow]; ring
  have h4 : Real.sqrt (|S.det| * |g.det| ^ 2) = 1 := by rw [h3]; simp
  rwa [Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq (abs_nonneg _)] at h4

/- English proof (translation)
Introduce `ι _ _ S P hS hdet hP hPS`. Take `⟨g, e, hg, he, hgP, hgS⟩` from `GlobalTheory.CompanionTheory.SW.Diag.simultaneous_normal_form_majorant ι S P hS hdet hP hPS`. Use `⟨fun τ => ∏ i, ((beta τ (e i))⁻¹) ^ (1 / 2 : ℂ), fun τ hτ => ?_⟩` and prove the remaining obligations. Establish `hτ0 : τ ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hτ`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 Real.pi_ne_zero`. Establish `hBre : ∀ i, 0 < ((Real.pi : ℂ) * beta τ (e i)).re` using `fun i => by`. Rewrite using `[Complex.re_ofReal_mul, beta_re]`. Conclude with `mul_pos Real.pi_pos hτ`.

Establish `hcont : ∀ A : Matrix ι ι ℝ, Continuous fun x : ι → ℝ => ((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ)`. Introduce `A`. Apply `Complex.continuous_ofReal.comp` to reduce the goal to its premises. Use `fun_prop`. Establish `hG : Continuous fun x : ι → ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ))` using `Complex.continuous_exp.comp ((continuous_const.mul (hcont S)).sub (continuous_const.mul (hcont P)))`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [norm_prod]`. Rewrite using `[Finset.prod_congr rfl fun i _ => norm_half τ (he i), Finset.prod_const, inv_pow]`. Both sides reduce to the same expression. Use `show (∏ i, ((beta τ (e i))⁻¹) ^ (1 / 2 : ℂ)) * (∏ i, ((beta (-τ⁻¹) (e i))⁻¹) ^ (1 / 2 : ℂ)) = 1`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[beta_inv hτ0 (he i)]`. Conclude with `half_mul (by rw [beta_re]; exact hτ)`. Apply `(subst g hg _ hG).1` to reduce the goal to its premises.

Establish `h` using `GaussianFourier.integrable_cexp_neg_sum_mul_add hBre (fun _ => 0)`. Use `h.congr (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [zero_mul, Finset.sum_const_zero, add_zero]`. Rewrite using `[quad hgS hgP]`. Introduce `y`.

Take `⟨v, rfl⟩ : ∃ v, g *ᵥ v = y` from `⟨g⁻¹ *ᵥ y, by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg), Matrix.one_mulVec]⟩`. Establish `hL : Continuous fun x : ι → ℝ => ((x ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ)`. Apply `Complex.continuous_ofReal.comp` to reduce the goal to its premises. Use `fun_prop`.

Establish `hFc : Continuous fun x : ι → ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ))` using `hG.mul (Complex.continuous_exp.comp (continuous_const.mul hL))`. Establish `h2` using `(subst g hg _ hFc).2`. Establish `h3 : ∫ u : ι → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ u)) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * (((g *ᵥ u) ⬝ᵥ (P *ᵥ (g *ᵥ u)) : ℝ) : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ)) = ∏ i, ( …`. Rewrite using `[← GaussianFourier.integral_cexp_neg_sum_mul_add hBre]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← Complex.exp_add, quad hgS hgP, lin hgS]`. Rewrite `h2` using `[h3]`. Establish `hd : (|g.det| : ℝ) ≠ 0` using `abs_ne_zero.2 hg`. Establish `hI : ∫ x : ι → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ)) = ((|g.det| : ℝ) : ℂ) * ∏ i, (((Real.pi : ℂ …`.

Establish `hu : ((|g.det| : ℝ) : ℂ) * ((|g.det|⁻¹ : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, mul_inv_cancel₀ hd, Complex.ofReal_one]`. Rewrite using `[h2, ← mul_assoc ((|g.det| : ℝ) : ℂ), hu, one_mul]`. Establish `hs : ((Real.sqrt |S.det| : ℝ) : ℂ) * ((|g.det| : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, det_scale he hgS, Complex.ofReal_one]`.

Rewrite using `[hI, ← mul_assoc ((Real.sqrt |S.det| : ℝ) : ℂ), hs, one_mul, Finset.prod_mul_distrib, quad hgS hgP (-τ⁻¹) v]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[div_mul_cancel_left₀ hpi]`. Rewrite using `[← Complex.exp_sum, ← Finset.sum_neg_distrib]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hb0 : beta τ (e i) ≠ 0`. Introduce `h0`. Use `beta_re τ (e := e i)` as an intermediate fact.

Rewrite `this` using `[h0]`. Simplify using `at this`. Conclude with `hτ.ne this`. Establish `he2 : ((e i : ℝ) : ℂ) ^ 2 = 1`. Apply the tactic sequence `rcases he i with h | h <;> simp [h]`.

Rewrite using `[beta_inv hτ0 (he i), mul_pow, mul_pow, mul_pow, Complex.I_sq, he2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_gaussian_real_place : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S P : Matrix ι ι ℝ), S.IsSymm → S.det ≠ 0 → P.PosDef → P * S⁻¹ * P = S → ∃ c : ℂ → ℂ, ∀ τ : ℂ, 0 < τ.im → ‖c τ‖ = (Real.sqrt ‖τ‖ ^ Fintype.card ι)⁻¹ ∧ c τ * c (-τ⁻¹) = 1 ∧ Integrable (fun x : ι → ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ))) ∧ ∀ y : ι → ℝ, ((Real.sqrt |S.det| : ℝ) : ℂ) * ∫ x : ι → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (S *ᵥ y) : ℝ) : ℂ)) = c τ * Complex.exp ((Real.pi : ℂ) * Complex.I * ((-τ⁻¹).re : ℂ) * ((y ⬝ᵥ (S *ᵥ y) : ℝ) : ℂ) - (Real.pi : ℂ) * ((-τ⁻¹).im : ℂ) * ((y ⬝ᵥ (P *ᵥ y) : ℝ) : ℂ)) := by
  intro ι _ _ S P hS hdet hP hPS
  obtain ⟨g, e, hg, he, hgP, hgS⟩ := GlobalTheory.CompanionTheory.SW.Diag.simultaneous_normal_form_majorant ι S P hS hdet hP hPS
  refine ⟨fun τ => ∏ i, ((beta τ (e i))⁻¹) ^ (1 / 2 : ℂ), fun τ hτ => ?_⟩
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hBre : ∀ i, 0 < ((Real.pi : ℂ) * beta τ (e i)).re := fun i => by
    rw [Complex.re_ofReal_mul, beta_re]
    exact mul_pos Real.pi_pos hτ
  have hcont : ∀ A : Matrix ι ι ℝ, Continuous fun x : ι → ℝ => ((x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) := by
    intro A
    apply Complex.continuous_ofReal.comp
    fun_prop
  have hG : Continuous fun x : ι → ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) *
      ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul (hcont S)).sub (continuous_const.mul (hcont P)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [norm_prod]
    rw [Finset.prod_congr rfl fun i _ => norm_half τ (he i), Finset.prod_const, inv_pow]
    rfl
  · show (∏ i, ((beta τ (e i))⁻¹) ^ (1 / 2 : ℂ)) *
      (∏ i, ((beta (-τ⁻¹) (e i))⁻¹) ^ (1 / 2 : ℂ)) = 1
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [beta_inv hτ0 (he i)]
    exact half_mul (by rw [beta_re]; exact hτ)
  · apply (subst g hg _ hG).1
    have h := GaussianFourier.integrable_cexp_neg_sum_mul_add hBre (fun _ => 0)
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [zero_mul, Finset.sum_const_zero, add_zero]
    rw [quad hgS hgP]
  · intro y
    obtain ⟨v, rfl⟩ : ∃ v, g *ᵥ v = y := ⟨g⁻¹ *ᵥ y, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg),
        Matrix.one_mulVec]⟩
    have hL : Continuous fun x : ι → ℝ =>
        ((x ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ) := by
      apply Complex.continuous_ofReal.comp
      fun_prop
    have hFc : Continuous fun x : ι → ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) *
          ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) *
          ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ)) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ)) :=
      hG.mul (Complex.continuous_exp.comp (continuous_const.mul hL))
    have h2 := (subst g hg _ hFc).2
    have h3 : ∫ u : ι → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) *
          (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ u)) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) *
          (((g *ᵥ u) ⬝ᵥ (P *ᵥ (g *ᵥ u)) : ℝ) : ℂ)) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ))
        = ∏ i, (((Real.pi : ℂ) / ((Real.pi : ℂ) * beta τ (e i))) ^ (1 / 2 : ℂ) *
            Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (e i : ℂ) * (v i : ℂ)) ^ 2 /
              (4 * ((Real.pi : ℂ) * beta τ (e i))))) := by
      rw [← GaussianFourier.integral_cexp_neg_sum_mul_add hBre]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only
      rw [← Complex.exp_add, quad hgS hgP, lin hgS]
    rw [h3] at h2
    have hd : (|g.det| : ℝ) ≠ 0 := abs_ne_zero.2 hg
    have hI : ∫ x : ι → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) *
          ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) - (Real.pi : ℂ) * (τ.im : ℂ) *
          ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ)) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ))
        = ((|g.det| : ℝ) : ℂ) * ∏ i, (((Real.pi : ℂ) / ((Real.pi : ℂ) * beta τ (e i))) ^ (1 / 2 : ℂ) *
            Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (e i : ℂ) * (v i : ℂ)) ^ 2 /
              (4 * ((Real.pi : ℂ) * beta τ (e i))))) := by
      have hu : ((|g.det| : ℝ) : ℂ) * ((|g.det|⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hd, Complex.ofReal_one]
      rw [h2, ← mul_assoc ((|g.det| : ℝ) : ℂ), hu, one_mul]
    have hs : ((Real.sqrt |S.det| : ℝ) : ℂ) * ((|g.det| : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, det_scale he hgS, Complex.ofReal_one]
    rw [hI, ← mul_assoc ((Real.sqrt |S.det| : ℝ) : ℂ), hs, one_mul,
      Finset.prod_mul_distrib, quad hgS hgP (-τ⁻¹) v]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [div_mul_cancel_left₀ hpi]
    · rw [← Complex.exp_sum, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hb0 : beta τ (e i) ≠ 0 := by
        intro h0
        have := beta_re τ (e := e i)
        rw [h0] at this
        simp at this
        exact hτ.ne this
      have he2 : ((e i : ℝ) : ℂ) ^ 2 = 1 := by
        rcases he i with h | h <;> simp [h]
      rw [beta_inv hτ0 (he i), mul_pow, mul_pow, mul_pow, Complex.I_sq, he2]
      field_simp
      ring

end GlobalTheory.CompanionTheory.SW.GaussOne
