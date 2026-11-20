import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

/- English proof (translation)
The claim follows from `Complex.ofRealCLM.hasFDerivAt.comp y (hasStrictFDerivAt_norm_sq y).hasFDerivAt`.
-/
theorem inh_hasFDerivAt_normSq (n : ℕ) (y : V n) :
    HasFDerivAt (fun y : V n => ((‖y‖ ^ 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (2 • innerSL ℝ y)) y :=
  Complex.ofRealCLM.hasFDerivAt.comp y (hasStrictFDerivAt_norm_sq y).hasFDerivAt

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `wdb`. Rewrite using `[(inh_hasFDerivAt_normSq n y).fderiv]`. Establish `hr : ∀ v : V n, (inner ℝ y v : ℝ) = (inner ℂ y v).re` using `fun v => by`. Simplify using `[PiLp.inner_apply, Complex.re_sum]`.

Simplify using `only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, Complex.ofRealCLM_apply, bas, hr, EuclideanSpace.inner_single_right, inner_smul_right, nsmul_eq_mul]`. Apply the tactic sequence `apply Complex.ext <;> simp`.
-/
theorem inh_wdb_normSq (n : ℕ) (k : Fin n) :
    wdb n k (fun y : V n => ((‖y‖ ^ 2 : ℝ) : ℂ)) = fun y => y k := by
  funext y
  unfold wdb
  rw [(inh_hasFDerivAt_normSq n y).fderiv]
  have hr : ∀ v : V n, (inner ℝ y v : ℝ) = (inner ℂ y v).re := fun v => by
    simp [PiLp.inner_apply, Complex.re_sum]
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, bas, hr, EuclideanSpace.inner_single_right,
    inner_smul_right, nsmul_eq_mul]
  apply Complex.ext <;> simp

/- English proof (translation)
Establish `h : (fun y : V n => y k) = ⇑((EuclideanSpace.proj k : V n →L[ℂ] ℂ).restrictScalars ℝ)`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Unfold `wd`. Rewrite using `[h, ContinuousLinearMap.fderiv]`.

Simplify using `only [ContinuousLinearMap.coe_restrictScalars', bas]`. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hjk, Ne.symm hjk]`.
-/
theorem inh_wd_coord (n : ℕ) (j k : Fin n) (y : V n) :
    wd n j (fun y : V n => y k) y = if j = k then 1 else 0 := by
  have h : (fun y : V n => y k) = ⇑((EuclideanSpace.proj k : V n →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext y; simp
  unfold wd
  rw [h, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', bas]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]

/- English proof (translation)
Introduce `_ _` and use `rfl`.
-/
theorem inh_isChart_refl (n : ℕ) : IsChart n id (OpenPartialHomeomorph.refl (V n)) :=
  fun _ _ => rfl

/- English proof (translation)
Use `⟨{ z := id isLocalHomeomorph := (Homeomorph.refl (V n)).isLocalHomeomorph e := fun y => ‖y‖ ^ 2 smooth_e := ?_ levi_e := ?_ isCompact_le := ?_ }⟩` and prove the remaining obligations. Introduce `e he`. Establish `hg : ContDiff ℝ ∞ (fun y : V n => ((‖y‖ ^ 2 : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℂ)`. Use `hg.contDiffOn.congr fun y hy => ?_` and prove the remaining obligations. Establish `h1` using `chart_z_symm n id e he y hy`.

Simplify using `only [id] at h1`. Simplify using `[Function.comp, h1]`. Introduce `x ξ`. Rewrite using `[levi_eq_leviV n id _ (inh_isChart_refl n) _ x (Set.mem_univ x) ξ]`. Unfold `leviV`.

Simplify using `only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id]`. Repeatedly rewrite using `[inh_wdb_normSq, inh_wd_coord]`. Simplify using `only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_nonneg fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.mul_conj]`. Simplify using `[Complex.normSq_nonneg]`. Introduce `a`. Use `Metric.isCompact_of_isClosed_isBounded (isClosed_le (continuous_norm.pow 2) continuous_const) ?_` and prove the remaining obligations. Use `isBounded_iff_forall_norm_le.2 ⟨max 1 a, fun x hx => ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_ofPred_eq] at hx`. Distinguish the cases in `h : ‖x‖ ≤ 1`. Conclude with `le_max_of_le_left h`. Use `push Not at h`. Conclude with `le_max_of_le_right (by nlinarith)`.
-/
theorem etaleStein_nonempty (n : ℕ) :
    InhabitedStatement n := by
  refine ⟨{ z := id
            isLocalHomeomorph := (Homeomorph.refl (V n)).isLocalHomeomorph
            e := fun y => ‖y‖ ^ 2
            smooth_e := ?_
            levi_e := ?_
            isCompact_le := ?_ }⟩
  · intro e he
    have hg : ContDiff ℝ ∞ (fun y : V n => ((‖y‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℂ)
    refine hg.contDiffOn.congr fun y hy => ?_
    have h1 := chart_z_symm n id e he y hy
    simp only [id] at h1
    simp [Function.comp, h1]
  · intro x ξ
    rw [levi_eq_leviV n id _ (inh_isChart_refl n) _ x (Set.mem_univ x) ξ]
    unfold leviV
    simp only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id]
    simp_rw [inh_wdb_normSq, inh_wd_coord]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  · intro a
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_le (continuous_norm.pow 2) continuous_const) ?_
    refine isBounded_iff_forall_norm_le.2 ⟨max 1 a, fun x hx => ?_⟩
    simp only [Set.mem_ofPred_eq] at hx
    by_cases h : ‖x‖ ≤ 1
    · exact le_max_of_le_left h
    · push Not at h
      exact le_max_of_le_right (by nlinarith)

end

end ReciprocityTheory.L2DbarEstimates
