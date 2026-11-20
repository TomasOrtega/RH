import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

/- English proof (translation)
Unfold `spherePoint`. Use `fun_prop`.
-/
theorem continuous_spherePoint (n : ℕ) : Continuous (spherePoint : UnitSphereC n → Fin n → ℂ) := by
  unfold spherePoint
  fun_prop

/- English proof (translation)
Establish `hn : 0 < n`. Break down `Nat.eq_zero_or_pos n with rfl | h` into its components or cases. Simplify using `[EuclideanSpace.norm_eq] at hu`. Conclude with `h`. Use `haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) := Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [hn])`.

Establish `h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0`. Rewrite using `[Measure.toSphere_apply_univ]`. Use `mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'` and prove the remaining obligations. Conclude with `Module.finrank_pos.ne'` after adjusting the coercions. Establish `htop : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤`.

Rewrite using `[Measure.toSphere_apply_univ]`. Conclude with `ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne`. Use `haveI : IsProbabilityMeasure (sphereProb n) := ProbabilityTheory.cond_isProbabilityMeasure_of_finite h0 htop`. Use `set μ := sphereProb n with hμ`. Use `set Z := {z : UnitSphereC n | MvPolynomial.eval (spherePoint z) g = 0} with hZdef`.

Establish `hZ : MeasurableSet Z` using `(isClosed_eq ((MvPolynomial.continuous_eval g).comp (continuous_spherePoint n)) continuous_const).measurableSet`. Take `⟨hint, -⟩` from `hSJ n a g u hg hu hgu`. Establish `key : ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤ (∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ) - Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ + (a : ℝ) / 2 * (harmonic (n - 1) : ℝ)`. Introduce `c hc`. Establish `hgc : (MvPolynomial.C c * g).IsHomogeneous a`.

Simplify using `using (MvPolynomial.isHomogeneous_C (Fin n) c).mul hg`. Take `⟨-, hle⟩` from `hSJ n a (MvPolynomial.C c * g) u hgc hu (by simp [hc, hgu])`. Simplify using `only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hle`. Establish `hpt : ∀ z : UnitSphereC n, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ = Zᶜ.indicator (fun _ ↦ Real.log ‖c‖) z + Real.log ‖MvPolynomial.eval (spherePoint z) g‖`. Introduce `z`.

Distinguish the cases in `hz : MvPolynomial.eval (spherePoint z) g = 0`. Establish `hzZ : z ∈ Z` using `hz`. Simplify using `[Set.indicator_apply, hzZ, hz]`. Establish `hzZ : z ∈ Zᶜ` using `hz`. Rewrite using `[Set.indicator_of_mem hzZ, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]`.

Establish `hI : ∫ z, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ ∂μ = (μ Zᶜ).toReal * Real.log ‖c‖ + ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ`. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_add ((integrable_const _).indicator hZ.compl) hint, integral_indicator_const _ hZ.compl, smul_eq_mul]`. Apply the tactic sequence `try rfl`. Establish `hcomp : (μ Zᶜ).toReal = 1 - (μ Z).toReal`.

Rewrite using `[prob_compl_eq_one_sub hZ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]`. Establish `hL : Real.log ‖c * MvPolynomial.eval (WithLp.ofLp u) g‖ = Real.log ‖c‖ + Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖`. Rewrite using `[norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hgu)]`. Rewrite `hle` using `[hI, hcomp, hL]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨K, hK⟩ : ∃ K : ℝ, ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤ K` from `⟨_, key⟩`. Assume the negation of the conclusion as `hne`. Establish `hp : 0 < (μ Z).toReal` using `ENNReal.toReal_pos hne (measure_ne_top _ _)`. Establish `h1` using `hK ((Real.exp ((|K| + 1) / (μ Z).toReal) : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')`. Rewrite `h1` using `[Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.log_exp]`.

Establish `h2 : (μ Z).toReal * ((|K| + 1) / (μ Z).toReal) = |K| + 1`. Clear the denominators using the available nonvanishing facts. Combine the linear relations using `[le_abs_self K]`.
-/
theorem sphere_zero_null (hSJ : SJStatement) {n a : ℕ} (g : MvPolynomial (Fin n) ℂ)
    (hg : g.IsHomogeneous a) (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1)
    (hgu : MvPolynomial.eval (WithLp.ofLp u) g ≠ 0) :
    sphereProb n {z | MvPolynomial.eval (spherePoint z) g = 0} = 0 := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [EuclideanSpace.norm_eq] at hu
    · exact h
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [hn])
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
    exact_mod_cast Module.finrank_pos.ne'
  have htop : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  haveI : IsProbabilityMeasure (sphereProb n) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite h0 htop
  set μ := sphereProb n with hμ
  set Z := {z : UnitSphereC n | MvPolynomial.eval (spherePoint z) g = 0} with hZdef
  have hZ : MeasurableSet Z :=
    (isClosed_eq ((MvPolynomial.continuous_eval g).comp (continuous_spherePoint n))
      continuous_const).measurableSet
  obtain ⟨hint, -⟩ := hSJ n a g u hg hu hgu
  have key : ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤
      (∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ) -
        Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ + (a : ℝ) / 2 * (harmonic (n - 1) : ℝ) := by
    intro c hc
    have hgc : (MvPolynomial.C c * g).IsHomogeneous a := by
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) c).mul hg
    obtain ⟨-, hle⟩ := hSJ n a (MvPolynomial.C c * g) u hgc hu (by simp [hc, hgu])
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hle
    have hpt : ∀ z : UnitSphereC n, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ =
        Zᶜ.indicator (fun _ ↦ Real.log ‖c‖) z + Real.log ‖MvPolynomial.eval (spherePoint z) g‖ := by
      intro z
      by_cases hz : MvPolynomial.eval (spherePoint z) g = 0
      · have hzZ : z ∈ Z := hz
        simp [Set.indicator_apply, hzZ, hz]
      · have hzZ : z ∈ Zᶜ := hz
        rw [Set.indicator_of_mem hzZ, norm_mul,
          Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]
    have hI : ∫ z, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ ∂μ =
        (μ Zᶜ).toReal * Real.log ‖c‖ + ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ := by
      simp_rw [hpt]
      rw [integral_add ((integrable_const _).indicator hZ.compl) hint,
        integral_indicator_const _ hZ.compl, smul_eq_mul]
      try rfl
    have hcomp : (μ Zᶜ).toReal = 1 - (μ Z).toReal := by
      rw [prob_compl_eq_one_sub hZ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
    have hL : Real.log ‖c * MvPolynomial.eval (WithLp.ofLp u) g‖ =
        Real.log ‖c‖ + Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ := by
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hgu)]
    rw [hI, hcomp, hL] at hle
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤ K := ⟨_, key⟩
  by_contra hne
  have hp : 0 < (μ Z).toReal := ENNReal.toReal_pos hne (measure_ne_top _ _)
  have h1 := hK ((Real.exp ((|K| + 1) / (μ Z).toReal) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.log_exp] at h1
  have h2 : (μ Z).toReal * ((|K| + 1) / (μ Z).toReal) = |K| + 1 := by
    field_simp
  linarith [le_abs_self K]

end ReciprocityTheory.MultiplicativeHeights
