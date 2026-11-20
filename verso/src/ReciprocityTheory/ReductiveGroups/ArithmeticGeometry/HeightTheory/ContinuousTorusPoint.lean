import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed

section

variable {K : Type} [Field K] [NumberField K] {κ : Type} [Fintype κ]

/- English proof (translation)
Introduce `h` and use `hf ((MvPolynomial.map_injective σ σ.injective) (by rw [h, map_zero]))`.
-/
theorem map_ne_zero_of_ne_zero {f : MvPolynomial κ K} (hf : f ≠ 0) (σ : K →+* ℂ) :
    MvPolynomial.map σ f ≠ 0 := fun h => hf ((MvPolynomial.map_injective σ σ.injective) (by rw [h, map_zero]))

end

/- English proof (translation)
Unfold `h0 hTX5`. Apply `div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Use `add_le_add le_rfl (Finset.sum_le_sum fun σ _ => ?_)` and prove the remaining obligations. Conclude with `sphereLeTorus B n a _ hn (map_ne_zero_of_ne_zero hf σ) (isMultiHomogeneous_map_ring a f ha σ)`.
-/
theorem logHeight_le_torusHeight {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) :
    h0 f ≤ hTX5 f := by
  unfold h0 hTX5
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine add_le_add le_rfl (Finset.sum_le_sum fun σ _ => ?_)
  exact sphereLeTorus B n a _ hn (map_ne_zero_of_ne_zero hf σ) (isMultiHomogeneous_map_ring a f ha σ)

/- English proof (translation)
Unfold `torusPoint`. Conclude with `continuous_pi fun i => Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i)))`.
-/
theorem continuous_torusPoint' {κ : Type} : Continuous (fun θ : κ → ℝ => torusPoint θ) := by
  unfold torusPoint
  exact continuous_pi fun i => Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i)))

/- English proof (translation)
The claim follows from `(Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval f).comp continuous_torusPoint')).measurable)`.
-/
theorem measurable_log_eval_torus {κ : Type} [Fintype κ] (f : MvPolynomial κ ℂ) :
    Measurable (fun θ : κ → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) := (Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval f).comp continuous_torusPoint')).measurable)

/- English proof (translation)
Establish `hmeas : Measurable (fun θ : κ' → ℝ => θ ∘ e)` using `measurable_pi_lambda _ (fun a => measurable_pi_apply (e a))`. Unfold `torusProb`. Use `symm`. Use `Measure.pi_eq (fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]`.

Establish `hpre : (fun θ : κ' → ℝ => θ ∘ e) ⁻¹' Set.univ.pi s = Set.univ.pi (Function.extend e s (fun _ => Set.univ))`. Use extensionality with `θ`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h y`.

Distinguish the cases in `hy : ∃ a, e a = y`. Take `⟨a, rfl⟩` from `hy`. Rewrite using `[he.extend_apply]`. Conclude with `h a`. Rewrite using `[Function.extend_apply' _ _ _ hy]`.

Discharge the goal by the elementary cases of `trivial`. Introduce `h a`. Establish `h1` using `h (e a)`. Rewrite `h1` using `[he.extend_apply]`. Then use the resulting hypothesis. Rewrite using `[hpre, Measure.pi_pi]`.

Use `set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)`. Establish `hν : ν Set.univ = 1` using `by simp [ν]`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.prod_subset (Finset.subset_univ _) (fun y _ hy => ?_)).symm` and prove the remaining obligations. Establish `hy' : ¬ ∃ a, e a = y` using `by simpa using hy`.

Rewrite using `[Function.extend_apply' _ _ _ hy', hν]`. Use `_ = ∏ a, ν (s a) := by`. Rewrite using `[Finset.prod_image (fun a _ b _ h => he h)]`. Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[he.extend_apply]`.
-/
theorem torusProb_map_comp {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) :
    Measure.map (fun θ : κ' → ℝ => θ ∘ e) (torusProb κ') = torusProb κ := by
  classical
  have hmeas : Measurable (fun θ : κ' → ℝ => θ ∘ e) :=
    measurable_pi_lambda _ (fun a => measurable_pi_apply (e a))
  unfold torusProb
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun θ : κ' → ℝ => θ ∘ e) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.extend e s (fun _ => Set.univ)) := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h y
      by_cases hy : ∃ a, e a = y
      · obtain ⟨a, rfl⟩ := hy
        rw [he.extend_apply]
        exact h a
      · rw [Function.extend_apply' _ _ _ hy]
        trivial
    · intro h a
      have h1 := h (e a)
      rwa [he.extend_apply] at h1
  rw [hpre, Measure.pi_pi]
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hν : ν Set.univ = 1 := by simp [ν]
  calc ∏ y, ν (Function.extend e s (fun _ => Set.univ) y)
      = ∏ y ∈ Finset.univ.image e, ν (Function.extend e s (fun _ => Set.univ) y) := by
        refine (Finset.prod_subset (Finset.subset_univ _) (fun y _ hy => ?_)).symm
        have hy' : ¬ ∃ a, e a = y := by simpa using hy
        rw [Function.extend_apply' _ _ _ hy', hν]
    _ = ∏ a, ν (s a) := by
        rw [Finset.prod_image (fun a _ b _ h => he h)]
        refine Finset.prod_congr rfl (fun a _ => ?_)
        rw [he.extend_apply]

/- English proof (translation)
Unfold `torusMean`. Repeatedly rewrite using `[MvPolynomial.eval_rename]`. Rewrite using `[← torusProb_map_comp e he, MeasureTheory.integral_map]`. Both sides reduce to the same expression. Conclude with `(measurable_pi_lambda _ fun i => measurable_pi_apply (e i)).aemeasurable`.

Conclude with `(measurable_log_eval_torus f).aestronglyMeasurable`.
-/
theorem torusMean_rename {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) (f : MvPolynomial κ ℂ) :
    torusMean (MvPolynomial.rename e f) = torusMean f := by
  unfold torusMean
  simp_rw [MvPolynomial.eval_rename]
  rw [← torusProb_map_comp e he, MeasureTheory.integral_map]
  · rfl
  · exact (measurable_pi_lambda _ fun i => measurable_pi_apply (e i)).aemeasurable
  · exact (measurable_log_eval_torus f).aestronglyMeasurable

/- English proof (translation)
Unfold `gaussAbs`. Rewrite using `[MvPolynomial.support_rename_of_injective he, Finset.sup_image]`. Use `congr 1`. Use `Finset.sup_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, MvPolynomial.coeff_rename_mapDomain e he]`.
-/
theorem gaussAbs_rename_of_injective {K : Type} [Field K] [NumberField K] {κ κ' : Type} (e : κ → κ')
    (he : Function.Injective e) (w : FinitePlace K) (f : MvPolynomial κ K) :
    gaussAbs w (MvPolynomial.rename e f) = gaussAbs w f := by
  classical
  unfold gaussAbs
  rw [MvPolynomial.support_rename_of_injective he, Finset.sup_image]
  congr 1
  refine Finset.sup_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, MvPolynomial.coeff_rename_mapDomain e he]

/- English proof (translation)
Unfold `hTX5`. Use `congr 2`. Conclude with `finsum_congr fun w => by rw [gaussAbs_rename_of_injective e he w f]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.map_rename, torusMean_rename e he]`.
-/
theorem hTX5_rename {K : Type} [Field K] [NumberField K] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ → κ') (he : Function.Injective e) (f : MvPolynomial κ K) :
    hTX5 (MvPolynomial.rename e f) = hTX5 f := by
  unfold hTX5
  congr 2
  · exact finsum_congr fun w => by rw [gaussAbs_rename_of_injective e he w f]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [MvPolynomial.map_rename, torusMean_rename e he]

end ReciprocityTheory.ChartRestriction.G.T0
