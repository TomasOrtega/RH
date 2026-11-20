import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish `hpm : Continuous (fun z : PCoord ε → ℂ => pmat z)` using `by first`. Consider the case `exact (JacB.pmatLin ε).continuous_of_finiteDimensional`. Consider the case `exact (dpbE ε).continuous_of_finiteDimensional`. Consider the case `(refine continuous_pi fun a => continuous_pi fun b => ?_`. Unfold `pmat`.

Apply the tactic sequence `split_ifs <;> fun_prop)`. Establish `hmk : Continuous fun k : KG ε => toMK k` using `by first`. Consider the case `fun_prop`. Consider the case `(unfold toMK; fun_prop)`. Consider the case `exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`.

Consider the case `(unfold toMK toM; fun_prop)`. Establish `hM : Continuous fun p : (PCoord ε → ℂ) × KG ε => toMK p.2⁻¹ * pmat p.1 * toMK p.2` using `((hmk.comp continuous_snd.inv).matrix_mul (hpm.comp continuous_fst)).matrix_mul (hmk.comp continuous_snd)`. Establish `hPh : Continuous fun p : (PCoord ε → ℂ) × KG ε => Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)` using `continuous_potential_comp lam hM (fun p => ⟨adK p.2⁻¹ p.1, conj_pmat_eq_adK p.2 p.1⟩)`. Establish `hop : Continuous fun p : (PCoord ε → ℂ) × KG ε => T.op p.2` using `(continuous_subtype_val.comp T.cont).comp continuous_snd`. Establish `hF : Continuous fun p : (PCoord ε → ℂ) × KG ε => ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) * (⟪T.op p.2 T.w, v⟫_ℂ * ⟪u, T.op p.2 T.w⟫_ℂ)` using `(Complex.continuous_ofReal.comp (Real.continuous_exp.comp hPh.neg)).mul (((hop.clm_apply continuous_const).inner continuous_const).mul (continuous_const.inner (hop.clm_apply continuous_const)))`.

Establish `hI` using `continuous_parametric_integral_of_continuous (μ := dk ε) (f := fun (z : PCoord ε → ℂ) (k : KG ε) => ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) * (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ)) hF isCompact_univ`. Simplify using `only [Measure.restrict_univ] at hI`. Establish `he : (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) = fun z => ((Module.finrank ℂ T.V : ℝ) : ℂ) * ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) * (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ) ∂(dk ε)`. Use function extensionality and compare the values at `z`. Conclude with `inner_fF_eq_integral lam T z u v`.

Rewrite using `[he]`. Conclude with `continuous_const.mul hI`.
-/
theorem fdl_inner_continuous {ε : Fin n → Bool} (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) (u v : T.V) :
    Continuous (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) := by
  have hpm : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
    first
    | exact (JacB.pmatLin ε).continuous_of_finiteDimensional
    | exact (dpbE ε).continuous_of_finiteDimensional
    | (refine continuous_pi fun a => continuous_pi fun b => ?_
       unfold pmat
       split_ifs <;> fun_prop)
  have hmk : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
    | (unfold toMK; fun_prop)
    | exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    | (unfold toMK toM; fun_prop)
  have hM : Continuous fun p : (PCoord ε → ℂ) × KG ε => toMK p.2⁻¹ * pmat p.1 * toMK p.2 :=
    ((hmk.comp continuous_snd.inv).matrix_mul (hpm.comp continuous_fst)).matrix_mul
      (hmk.comp continuous_snd)
  have hPh : Continuous fun p : (PCoord ε → ℂ) × KG ε => Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2) :=
    continuous_potential_comp lam hM (fun p => ⟨adK p.2⁻¹ p.1, conj_pmat_eq_adK p.2 p.1⟩)
  have hop : Continuous fun p : (PCoord ε → ℂ) × KG ε => T.op p.2 :=
    (continuous_subtype_val.comp T.cont).comp continuous_snd
  have hF : Continuous fun p : (PCoord ε → ℂ) × KG ε =>
      ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) *
        (⟪T.op p.2 T.w, v⟫_ℂ * ⟪u, T.op p.2 T.w⟫_ℂ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hPh.neg)).mul
      (((hop.clm_apply continuous_const).inner continuous_const).mul
        (continuous_const.inner (hop.clm_apply continuous_const)))
  have hI := continuous_parametric_integral_of_continuous (μ := dk ε)
    (f := fun (z : PCoord ε → ℂ) (k : KG ε) =>
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
        (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ)) hF isCompact_univ
  simp only [Measure.restrict_univ] at hI
  have he : (fun z : PCoord ε → ℂ => ⟪u, fF ε lam T (pmat z) v⟫_ℂ) = fun z =>
      ((Module.finrank ℂ T.V : ℝ) : ℂ) *
        ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) *
          (⟪T.op k T.w, v⟫_ℂ * ⟪u, T.op k T.w⟫_ℂ) ∂(dk ε) := by
    funext z
    exact inner_fF_eq_integral lam T z u v
  rw [he]
  exact continuous_const.mul hI

/- English proof (translation)
Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf) (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => h0 i (x i)))), integral_fintype_prod_eq_prod]`. Conclude with `ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))`.
-/
theorem fdl_lint_pi_ofReal {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (h0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ENNReal.ofReal (∫ x, f i x ∂(μ i)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hf)
      (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => h0 i (x i)))),
    integral_fintype_prod_eq_prod]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (h0 i))

/- English proof (translation)
Establish `h` using `GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hc`. Simplify using `only [neg_mul, Complex.finrank_real_complex] at h`. Rewrite using `[h]`. Evaluate the numerical expressions.
-/
theorem fdl_cgauss {c : ℝ} (hc : 0 < c) : ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2)) = Real.pi / c := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hc
  simp only [neg_mul, Complex.finrank_real_complex] at h
  rw [h]
  norm_num

/- English proof (translation)
Apply `Integrable.of_integral_ne_zero` to reduce the goal to its premises. Rewrite using `[fdl_cgauss hc]`. Conclude with `(div_pos Real.pi_pos hc).ne'`.
-/
theorem fdl_cgauss_int {c : ℝ} (hc : 0 < c) : Integrable (fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2))) := by
  apply Integrable.of_integral_ne_zero
  rw [fdl_cgauss hc]
  exact (div_pos Real.pi_pos hc).ne'

/- English proof (translation)
Take `⟨⟨a, b⟩, hab⟩` from `ab`. Establish `h : (b : ℕ) < (a : ℕ)` using `hab.1`. Establish `h' : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ)` using `by exact_mod_cast h`. Use `show 0 < (0 : Fin n → ℝ) b - (0 : Fin n → ℝ) a + ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)`. Simplify using `only [Pi.zero_apply, sub_zero, zero_add]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fdl_wab_zero_pos {ε : Fin n → Bool} (ab : PCoord ε) : 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by
  obtain ⟨⟨a, b⟩, hab⟩ := ab
  have h : (b : ℕ) < (a : ℕ) := hab.1
  have h' : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast h
  show 0 < (0 : Fin n → ℝ) b - (0 : Fin n → ℝ) a + ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)
  simp only [Pi.zero_apply, sub_zero, zero_add]
  linarith

/- English proof (translation)
Establish `hw : ∀ ab : PCoord ε, 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2` using `fdl_wab_zero_pos`. Establish `h1 : ∀ y : PCoord ε → ℂ, Real.exp (-Qf (0 : Fin n → ℝ) y) = ∏ ab, Real.exp (-(wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖y ab‖ ^ 2))`. Introduce `y`. Rewrite using `[Qf, ← Finset.sum_neg_distrib, Real.exp_sum]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[MeasureTheory.volume_pi]`. Rewrite using `[fdl_lint_pi_ofReal (E := fun _ : PCoord ε => ℂ) (μ := fun _ => volume) (fun (ab : PCoord ε) (x : ℂ) => Real.exp (-(wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖x‖ ^ 2))) (fun ab => fdl_cgauss_int (hw ab)) (fun _ _ => (Real.exp_pos _).le)]`. Rewrite using `[PiW, ENNReal.ofReal_prod_of_nonneg (fun ab _ => (div_pos Real.pi_pos (hw ab)).le)]`. Conclude with `Finset.prod_congr rfl fun ab _ => by rw [fdl_cgauss (hw ab)]`.
-/
theorem fdl_gauss (ε : Fin n → Bool) :
    ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) = ENNReal.ofReal (PiW ε 0) := by
  have hw : ∀ ab : PCoord ε, 0 < wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := fdl_wab_zero_pos
  have h1 : ∀ y : PCoord ε → ℂ, Real.exp (-Qf (0 : Fin n → ℝ) y) =
      ∏ ab, Real.exp (-(wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖y ab‖ ^ 2)) := by
    intro y
    rw [Qf, ← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [h1]
  rw [MeasureTheory.volume_pi]
  rw [fdl_lint_pi_ofReal (E := fun _ : PCoord ε => ℂ) (μ := fun _ => volume)
    (fun (ab : PCoord ε) (x : ℂ) => Real.exp (-(wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 * ‖x‖ ^ 2)))
    (fun ab => fdl_cgauss_int (hw ab)) (fun _ _ => (Real.exp_pos _).le)]
  rw [PiW, ENNReal.ofReal_prod_of_nonneg (fun ab _ => (div_pos Real.pi_pos (hw ab)).le)]
  exact Finset.prod_congr rfl fun ab _ => by rw [fdl_cgauss (hw ab)]

end ReciprocityTheory.ChartRestriction.DS
