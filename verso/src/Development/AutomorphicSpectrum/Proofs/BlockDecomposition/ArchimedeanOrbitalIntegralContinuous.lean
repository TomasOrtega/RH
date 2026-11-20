import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

/- English proof (translation)
Unfold `phaseM`. Use `continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_` and prove the remaining obligations. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramC]`. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => ?_` and prove the remaining obligations. Use `continuous_const.mul ?_` and prove the remaining obligations.

Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun X : W → Fin n → Fin M → ℂ => X w c i` using `by fun_prop`. Establish `h2 : Continuous fun X : W → Fin n → Fin M → ℂ => X w a j` using `by fun_prop`. Use `first`. Consider the case `exact ((Complex.continuous_conj.comp h1).mul continuous_const).mul (by fun_prop)`.

Consider the case `exact ((Complex.continuous_conj.comp h2).mul continuous_const).mul (by fun_prop)`.
-/
theorem continuous_phaseM_X {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (B : W → Matrix (Fin n) (Fin n) ℂ) :
    Continuous (phaseM J B) := by
  unfold phaseM
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramC]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => ?_
  refine continuous_const.mul ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have h1 : Continuous fun X : W → Fin n → Fin M → ℂ => X w c i := by fun_prop
  have h2 : Continuous fun X : W → Fin n → Fin M → ℂ => X w a j := by fun_prop
  first
    | exact ((Complex.continuous_conj.comp h1).mul continuous_const).mul (by fun_prop)
    | exact ((Complex.continuous_conj.comp h2).mul continuous_const).mul (by fun_prop)

/- English proof (translation)
Unfold `phaseM`. Use `continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_` and prove the remaining obligations. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply]`. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => ?_` and prove the remaining obligations. Use `Continuous.mul ?_ continuous_const` and prove the remaining obligations.

Establish `h0 : Continuous fun b : W → hermC n => (b w : Matrix (Fin n) (Fin n) ℂ)` using `continuous_subtype_val.comp (continuous_apply w)`. Establish `h1 : Continuous fun m : Matrix (Fin n) (Fin n) ℂ => m a c` using `(continuous_apply c).comp (continuous_apply a)`. Conclude with `h1.comp h0`.
-/
theorem continuous_phaseM_b {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (X : W → Fin n → Fin M → ℂ) :
    Continuous fun b : W → hermC n =>
      phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X := by
  unfold phaseM
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => ?_
  refine Continuous.mul ?_ continuous_const
  have h0 : Continuous fun b : W → hermC n => (b w : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_subtype_val.comp (continuous_apply w)
  have h1 : Continuous fun m : Matrix (Fin n) (Fin n) ℂ => m a c :=
    (continuous_apply c).comp (continuous_apply a)
  exact h1.comp h0

/- English proof (translation)
Use `haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes`. Establish `hs` using `Measure.isAddLeftInvariant_eq_smul (Measure.map e μ) (volume : Measure (Fin N → ℝ))`. Establish `hi : Integrable f (Measure.map e μ)`. Rewrite using `[hs]`. Conclude with `(f.integrable (μ := volume)).smul_measure_nnreal`.

Conclude with `hi.comp_measurable he.measurable`.
-/
theorem integrable_comp {E : Type} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]
    (N : ℕ) (e : E ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (fun X => f (e X)) μ := by
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hs := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ)
    (volume : Measure (Fin N → ℝ))
  have hi : Integrable f (Measure.map e μ) := by
    rw [hs]
    exact (f.integrable (μ := volume)).smul_measure_nnreal
  exact hi.comp_measurable he.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

/- English proof (translation)
Establish `hint` using `Cont.integrable_comp N e he hes f μ`. Establish `hg : Continuous fun X => f (e X)` using `f.continuous.comp he`. Establish `hnorm : ∀ t : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1`. Introduce `t`. Establish `: (2 * Real.pi * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`.

Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`. Unfold `coreC`. Use `continuous_of_dominated (bound := fun X => ‖f (e X)‖) ?_ ?_ hint.norm ?_` and prove the remaining obligations. Introduce `b`. Use `Continuous.aestronglyMeasurable (hg.mul ?_)` and prove the remaining obligations.

Use `Cont.continuous_phaseM_X J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ))` as an intermediate fact. Conclude with `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp this))`. Introduce `b`. Use `Filter.Eventually.of_forall fun X => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hnorm, mul_one]`.

Use `Filter.Eventually.of_forall fun X => ?_` and prove the remaining obligations. Conclude with `continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Cont.continuous_phaseM_b J X))))`.
-/
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz
    (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e)
    (hes : Continuous e.symm) (f : SchwartzMap (Fin N → ℝ) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure) :
    Continuous (coreC J μ (fun X => f (e X))) := by
  have hint := Cont.integrable_comp N e he hes f μ
  have hg : Continuous fun X => f (e X) := f.continuous.comp he
  have hnorm : ∀ t : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    have : (2 * Real.pi * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  unfold coreC
  refine continuous_of_dominated (bound := fun X => ‖f (e X)‖) ?_ ?_ hint.norm ?_
  · intro b
    refine Continuous.aestronglyMeasurable (hg.mul ?_)
    have := Cont.continuous_phaseM_X J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ))
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp this))
  · intro b
    refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, hnorm, mul_one]
  · refine Filter.Eventually.of_forall fun X => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (Cont.continuous_phaseM_b J X))))
