import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RotEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinSmoothContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PeriodicIntegralFundamentalDomainInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinPeriodDerivative
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermOfPeriodMeanOfUpperBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermAutomorphy
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinLieAlgebraAction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinCentralLieAction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinContinuousLeftAction

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis

namespace UpperTheory.V.Br

section Aff
variable {R : Type} [CommRing R]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
private theorem cm_aff_mul (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [aff]`.
-/
private theorem cm_aff_one : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]`.
-/
private theorem cm_scalar_comm (y : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) y = Matrix.GeneralLinearGroup.scalar (Fin 2) y * g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]

end Aff

/- English proof (translation)
Establish `h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-κ * t) * f t) 0 t` using `fun t => by`. Use `(((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-κ)).cexp).mul (h t)` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Complex.ofRealCLM_apply, Complex.ofReal_one]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2` using `is_const_of_deriv_eq_zero (fun t => (h1 t).differentiableAt) (fun t => (h1 t).deriv) 1 0`. Simplify using `only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2`. Rewrite using `[← h2, ← mul_assoc, ← Complex.exp_add]`. Simplify using the standard rewrite rules.
-/
private theorem cm_ode {f : ℝ → ℂ} {κ : ℂ} (h : ∀ t, HasDerivAt f (κ * f t) t) : f 1 = Complex.exp κ * f 0 := by
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-κ * t) * f t) 0 t := fun t => by
    have := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-κ)).cexp).mul (h t)
    refine this.congr_deriv ?_
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; ring
  have h2 := is_const_of_deriv_eq_zero (fun t => (h1 t).differentiableAt) (fun t => (h1 t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
  rw [← h2, ← mul_assoc, ← Complex.exp_add]; simp

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Unfold `cterm at hg ⊢`. Simplify using `only [← mul_assoc, hk]`. Rewrite using `[integral_const_mul, hg, mul_zero]`.
-/
private theorem cm_scal [MeasurableSpace (NA F)] (μ : Measure (NA F)) (D : Set (NA F)) (φ : GA F 2 → ℂ) {k : GA F 2} {z : ℂ}
    (hk : ∀ g, φ (g * k) = z * φ g) (g : GA F 2) (hg : cterm μ D φ g = 0) : cterm μ D φ (g * k) = 0 := by
  unfold cterm at hg ⊢
  simp only [← mul_assoc, hk]
  rw [integral_const_mul, hg, mul_zero]

variable [IsTotallyReal F]

/- English proof (translation)
Set `u : TR.Rinf F` to `fun v => Real.log (y.val v)`. Set `z : ℝ → (TR.Rinf F)ˣ` to `fun t => ⟨fun v => Real.exp (t * u v), fun v => Real.exp (-(t * u v)), by funext v; simp [← Real.exp_add], by funext v; simp [← Real.exp_add]⟩`. Establish `hz : ∀ s t, z (s + t) = z s * z t` using `fun s t => Units.ext (funext fun v => by simp [z, add_mul, Real.exp_add])`. Establish `h0 : z 0 = 1` using `Units.ext (funext fun v => by simp [z])`. Establish `h1 : z 1 = y` using `Units.ext (funext fun v => by simp [z, u, Real.exp_log (hy v)])`.

Use `cm_ode (f := fun t => ψ (TR.infGL F 2 (aff (z t) 0) * g)) (κ := (k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ)) fun t => by` as an intermediate fact. Establish `h2` using `h u z (fun _ _ => rfl) (TR.infGL F 2 (aff (z t) 0) * g)`. Establish `h3` using `HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h2)`. Use `h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[← mul_assoc, ← map_mul, cm_aff_mul, ← hz]`. Simplify using the standard rewrite rules. Rewrite `this` using `[h1, h0, cm_aff_one, map_one, one_mul, hg, mul_zero]`. Conclude with `this`.
-/
private theorem cm_arch {ψ : GA F 2 → ℂ} {k : ℕ} (h : ∀ (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ),
    (∀ t v, (y t).val v = Real.exp (t * u v)) → ∀ g,
    HasDerivAt (fun t => ψ (TR.infGL F 2 (aff (y t) 0) * g)) ((k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ) * ψ g) 0)
    (y : (TR.Rinf F)ˣ) (hy : ∀ v, 0 < y.val v) (g : GA F 2) (hg : ψ g = 0) :
    ψ (TR.infGL F 2 (aff y 0) * g) = 0 := by
  let u : TR.Rinf F := fun v => Real.log (y.val v)
  let z : ℝ → (TR.Rinf F)ˣ := fun t => ⟨fun v => Real.exp (t * u v), fun v => Real.exp (-(t * u v)),
    by funext v; simp [← Real.exp_add], by funext v; simp [← Real.exp_add]⟩
  have hz : ∀ s t, z (s + t) = z s * z t := fun s t => Units.ext (funext fun v => by simp [z, add_mul, Real.exp_add])
  have h0 : z 0 = 1 := Units.ext (funext fun v => by simp [z])
  have h1 : z 1 = y := Units.ext (funext fun v => by simp [z, u, Real.exp_log (hy v)])
  have := cm_ode (f := fun t => ψ (TR.infGL F 2 (aff (z t) 0) * g)) (κ := (k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ)) fun t => by
    have h2 := h u z (fun _ _ => rfl) (TR.infGL F 2 (aff (z t) 0) * g)
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h2)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    beta_reduce
    rw [← mul_assoc, ← map_mul, cm_aff_mul, ← hz]; simp
  rw [h1, h0, cm_aff_one, map_one, one_mul, hg, mul_zero] at this
  exact this

end UpperTheory.V.Br

/- English proof (translation)
Introduce `F _ _ _ _ _ μ _ D hD k c ω hω φ hφ M hM`. Establish `hB` using `UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock`. Establish `hL` using `UpperTheory.eisenstein_continuous_left_action UpperTheory.eisenstein_smooth_continuous hB (UpperTheory.constant_term_automorphy UpperTheory.eisenstein_smooth_continuous UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_period_derivative UpperTheory. …`. Take `⟨-, hN, hT⟩` from `hB F μ D hD φ.1 (UpperTheory.eisenstein_smooth_continuous F 2 φ hφ.aut.level) hφ.aut.left`. Use `⟨fun x g hg => (hN x g).trans hg, fun a g hg => (hT a g).trans hg, fun y hy g hg => cm_arch (hL F μ D hD k c ω hω φ hφ) y hy g hg, fun z g hg => ?_, fun u hu g hg => ?_, fun θ h hh g hg => ?_⟩` and prove the remaining obligations.

Rewrite using `[← cm_scalar_comm]`. Conclude with `cm_scal μ D φ.1 (fun g => by rw [cm_scalar_comm, hφ.cent]) g hg`. Conclude with `cm_scal μ D φ.1 (z := 1) (fun g => by rw [one_mul]; exact congrFun (congrArg Subtype.val (hM u hu)) g) g hg`. Conclude with `cm_scal μ D φ.1 (rotEig F φ _ hφ.wt θ h hh) g hg`.
-/
theorem UpperTheory.V.Br.ctMoves :
    UpperTheory.V.Br.CtMoves := by
  intro F _ _ _ _ _ μ _ D hD k c ω hω φ hφ M hM
  have hB := UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock
  have hL := UpperTheory.eisenstein_continuous_left_action UpperTheory.eisenstein_smooth_continuous hB (UpperTheory.constant_term_automorphy UpperTheory.eisenstein_smooth_continuous UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_period_derivative UpperTheory.eisenstein_constantTerm_upperBlock)
    UpperTheory.eisenstein_lie_algebra_action UpperTheory.eisenstein_central_lie_action
  obtain ⟨-, hN, hT⟩ := hB F μ D hD φ.1 (UpperTheory.eisenstein_smooth_continuous F 2 φ hφ.aut.level) hφ.aut.left
  refine ⟨fun x g hg => (hN x g).trans hg, fun a g hg => (hT a g).trans hg,
    fun y hy g hg => cm_arch (hL F μ D hD k c ω hω φ hφ) y hy g hg, fun z g hg => ?_, fun u hu g hg => ?_, fun θ h hh g hg => ?_⟩
  · rw [← cm_scalar_comm]
    exact cm_scal μ D φ.1 (fun g => by rw [cm_scalar_comm, hφ.cent]) g hg
  · exact cm_scal μ D φ.1 (z := 1) (fun g => by rw [one_mul]; exact congrFun (congrArg Subtype.val (hM u hu)) g) g hg
  · exact cm_scal μ D φ.1 (rotEig F φ _ hφ.wt θ h hh) g hg
