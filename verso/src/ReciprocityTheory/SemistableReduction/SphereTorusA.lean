import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Polynomial

/- English proof (translation)
Rewrite using `[logMahlerMeasure_def, Real.circleAverage, ← intervalIntegral.integral_of_le zero_le_one]`. Establish `h2 : (2 * Real.pi) ≠ 0` using `by positivity`. Use `intervalIntegral.integral_comp_mul_left (fun θ => Real.log ‖eval (circleMap 0 1 θ) q‖) (a := 0) (b := 1) h2` as an intermediate fact. Simplify using `only [mul_zero, mul_one] at this`. Rewrite using `[← this]`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Use `congr 3`. Simplify using `only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]`. Put the polynomial expressions in normal form.
-/
theorem integral_Ioc_log_eval_eq_logMahlerMeasure (q : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖q.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ =
      q.logMahlerMeasure := by
  rw [logMahlerMeasure_def, Real.circleAverage, ← intervalIntegral.integral_of_le zero_le_one]
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left
    (fun θ => Real.log ‖eval (circleMap 0 1 θ) q‖) (a := 0) (b := 1) h2
  simp only [mul_zero, mul_one] at this
  rw [← this]
  congr 1
  funext t
  congr 3
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring_nf

/- English proof (translation)
Distinguish the cases in `hp : p = 0`. Simplify using `[hp]`. Establish `hq : p.comp (C c * X) ≠ 0`. Introduce `h`. Apply `hp` to reduce the goal to its premises.

Establish `h'` using `congrArg (fun r => r.comp (C c⁻¹ * X)) h`. Establish `hX : (C c * X).comp (C c⁻¹ * X) = (X : ℂ[X])`. Simplify using `[← mul_assoc, ← C_mul, mul_inv_cancel₀ hc]`. Simplify `h'` using `[Polynomial.comp_assoc, hX]`. Establish `key : ∀ s : Multiset ℂ, (((s.map fun a => X - C a).prod).comp (C c * X)).mahlerMeasure ≤ ((s.map fun a => X - C a).prod).mahlerMeasure`.

Introduce `s`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Simplify using `only [Multiset.map_cons, Multiset.prod_cons, mul_comp, mahlerMeasure_mul]`.

Apply `mul_le_mul _ ih (mahlerMeasure_nonneg _) (mahlerMeasure_nonneg _)` to reduce the goal to its premises. Establish `h1 : (X - C a).comp (C c * X) = C c * X + C (-a)`. Simplify using `[sub_eq_add_neg]`. Rewrite using `[h1, mahlerMeasure_C_mul_X_add_C hc, mahlerMeasure_X_sub_C, norm_neg]`. Conclude with `max_le_max hc1 le_rfl`.

Rewrite using `[logMahlerMeasure_eq_log_MahlerMeasure, logMahlerMeasure_eq_log_MahlerMeasure]`. Apply `Real.log_le_log (mahlerMeasure_pos_of_ne_zero hq)` to reduce the goal to its premises. Establish `hs` using `(IsAlgClosed.splits p).eq_prod_roots`. Rewrite using `[hs, mul_comp, C_comp, mahlerMeasure_mul, mahlerMeasure_mul]`. Conclude with `mul_le_mul_of_nonneg_left (key _) (mahlerMeasure_nonneg _)`.
-/
theorem logMahlerMeasure_comp_C_mul_X_le (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    (p.comp (C c * X)).logMahlerMeasure ≤ p.logMahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  have hq : p.comp (C c * X) ≠ 0 := by
    intro h
    apply hp
    have h' := congrArg (fun r => r.comp (C c⁻¹ * X)) h
    have hX : (C c * X).comp (C c⁻¹ * X) = (X : ℂ[X]) := by
      simp [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc]
    simpa [Polynomial.comp_assoc, hX] using h'
  have key : ∀ s : Multiset ℂ, (((s.map fun a => X - C a).prod).comp (C c * X)).mahlerMeasure ≤
      ((s.map fun a => X - C a).prod).mahlerMeasure := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, mahlerMeasure_mul]
      apply mul_le_mul _ ih (mahlerMeasure_nonneg _) (mahlerMeasure_nonneg _)
      have h1 : (X - C a).comp (C c * X) = C c * X + C (-a) := by
        simp [sub_eq_add_neg]
      rw [h1, mahlerMeasure_C_mul_X_add_C hc, mahlerMeasure_X_sub_C, norm_neg]
      exact max_le_max hc1 le_rfl
  rw [logMahlerMeasure_eq_log_MahlerMeasure, logMahlerMeasure_eq_log_MahlerMeasure]
  apply Real.log_le_log (mahlerMeasure_pos_of_ne_zero hq)
  have hs := (IsAlgClosed.splits p).eq_prod_roots
  rw [hs, mul_comp, C_comp, mahlerMeasure_mul, mahlerMeasure_mul]
  exact mul_le_mul_of_nonneg_left (key _) (mahlerMeasure_nonneg _)

/- English proof (translation)
Establish `h` using `integral_Ioc_log_eval_eq_logMahlerMeasure (p.comp (C c * X))`. Simplify using `only [eval_comp, eval_mul, eval_C, eval_X] at h`. Rewrite using `[h, integral_Ioc_log_eval_eq_logMahlerMeasure]`. Conclude with `logMahlerMeasure_comp_C_mul_X_le p hc hc1`.
-/
theorem integral_log_eval_mul_le (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
        Real.log ‖p.eval (c * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ ≤
      ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ := by
  have h := integral_Ioc_log_eval_eq_logMahlerMeasure (p.comp (C c * X))
  simp only [eval_comp, eval_mul, eval_C, eval_X] at h
  rw [h, integral_Ioc_log_eval_eq_logMahlerMeasure]
  exact logMahlerMeasure_comp_C_mul_X_le p hc hc1

instance isProbabilityMeasure_restrict_Ioc_zero_one :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩

instance isProbabilityMeasure_torusProb_sphere (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusProb ι) := by
  unfold torusProb; infer_instance

/- English proof (translation)
Establish `hm : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)` using `measurable_update'`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Use `symm`. Apply `Measure.pi_eq` to reduce the goal to its premises. Introduce `s hs`.

Rewrite using `[Measure.map_apply hm (MeasurableSet.univ_pi hs)]`. Establish `hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) = (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i`. Use extensionality with `⟨x, t⟩`. Simplify using `only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun j => ?_, by simpa using h i⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify `h j` using `[Function.update_of_ne hj]`. Introduce and unpack `⟨h1, h2⟩ j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using h2`.

Simplify `h1 j` using `[Function.update_of_ne hj]`. Rewrite using `[hpre, Measure.prod_prod, torusProb, Measure.pi_pi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase (s := Finset.univ) (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j)) (Finset.mem_univ i)]`. Simplify using `only [Function.update_self, measure_univ, one_mul]`. Rewrite using `[mul_comm]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]`.
-/
theorem measurePreserving_update_torus {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) (torusProb ι) := by
  have hm : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) := measurable_update'
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [hpre, Measure.prod_prod, torusProb, Measure.pi_pi,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (s := Finset.univ) (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j))
      (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/- English proof (translation)
Establish `hU` using `measurePreserving_update_torus (ι := ι) i`. Establish `hgU : Integrable (g ∘ fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))` using `(hU.integrable_comp hg.aestronglyMeasurable).mpr hg`. Use `⟨hgU.integral_prod_left, ?_⟩` and prove the remaining obligations. Establish `h1 : ∫ θ, g θ ∂(torusProb ι) = ∫ p, g (Function.update p.1 i p.2) ∂((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))` using `by conv_lhs => rw [← hU.map_eq]`. Conclude with `integral_map hU.measurable.aemeasurable (by rw [hU.map_eq]; exact hg.aestronglyMeasurable)`.

Rewrite using `[h1]`. Conclude with `integral_prod _ hgU`.
-/
theorem integral_torus_eq_iter {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {g : (ι → ℝ) → ℝ}
    (hg : Integrable g (torusProb ι)) :
    Integrable (fun x => ∫ t in Set.Ioc (0 : ℝ) 1, g (Function.update x i t)) (torusProb ι) ∧
    ∫ θ, g θ ∂(torusProb ι) =
      ∫ x, (∫ t in Set.Ioc (0 : ℝ) 1, g (Function.update x i t)) ∂(torusProb ι) := by
  have hU := measurePreserving_update_torus (ι := ι) i
  have hgU : Integrable (g ∘ fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (hU.integrable_comp hg.aestronglyMeasurable).mpr hg
  refine ⟨hgU.integral_prod_left, ?_⟩
  have h1 : ∫ θ, g θ ∂(torusProb ι) = ∫ p, g (Function.update p.1 i p.2)
      ∂((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    conv_lhs => rw [← hU.map_eq]
    exact integral_map hU.measurable.aemeasurable (by rw [hU.map_eq]; exact hg.aestronglyMeasurable)
  rw [h1]
  exact integral_prod _ hgU

end ReciprocityTheory.MultiplicativeHeights
