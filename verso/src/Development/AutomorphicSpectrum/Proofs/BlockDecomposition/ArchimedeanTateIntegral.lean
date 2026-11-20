import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex

open MeasureTheory Ad3 Set Filter

namespace GlobalTheory.CompanionTheory.RealTateConv

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Conclude with `u.ne_zero`.

Introduce `hx`. Conclude with `⟨Units.mk0 x hx, rfl⟩`.
-/
theorem range_units_val : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

/- English proof (translation)
Use `⟨Units.val_injective, ?_, ?_⟩` and prove the remaining obligations. Conclude with `measurable_iff_comap_le.2 le_rfl`. Introduce `s hs`. Take `⟨t, ht, rfl⟩` from `hs`. Rewrite using `[Set.image_preimage_eq_inter_range, range_units_val]`.

Conclude with `ht.inter (measurableSet_singleton 0).compl`.
-/
theorem measurableEmbedding_units_val : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨Units.val_injective, ?_, ?_⟩
  · exact measurable_iff_comap_le.2 le_rfl
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [Set.image_preimage_eq_inter_range, range_units_val]
    exact ht.inter (measurableSet_singleton 0).compl

/- English proof (translation)
Establish `hm` using `measurableEmbedding_units_val`. Establish `hρ : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹` using `measurable_abs.inv.ennreal_ofReal`. Establish `hfull : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹).restrict (Set.range (Units.val : ℝˣ → ℝ)) = volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹`. Rewrite using `[range_units_val]`. Apply `Measure.restrict_eq_self_of_ae_mem` to reduce the goal to its premises.

Conclude with `(withDensity_absolutelyContinuous _ _).ae_le (compl_mem_ae_iff.2 (measure_singleton 0))`. Establish `h1 : Integrable (fun a : ℝˣ => g a) mulR ↔ Integrable g (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹)`. Rewrite using `[← hfull, ← hm.map_comap, hm.integrable_map_iff]`. Both sides reduce to the same expression. Rewrite using `[h1, integrable_withDensity_iff_integrable_smul' hρ (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]`.

Repeatedly rewrite using `[ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg _))]`.
-/
theorem integrable_mulR_iff (g : ℝ → ℂ) :
    Integrable (fun a : ℝˣ => g a) mulR ↔ Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
  have hm := measurableEmbedding_units_val
  have hρ : Measurable fun x : ℝ => ENNReal.ofReal |x|⁻¹ := measurable_abs.inv.ennreal_ofReal
  have hfull : (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹).restrict
      (Set.range (Units.val : ℝˣ → ℝ)) = volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ := by
    rw [range_units_val]
    apply Measure.restrict_eq_self_of_ae_mem
    exact (withDensity_absolutelyContinuous _ _).ae_le (compl_mem_ae_iff.2 (measure_singleton 0))
  have h1 : Integrable (fun a : ℝˣ => g a) mulR ↔
      Integrable g (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹) := by
    rw [← hfull, ← hm.map_comap, hm.integrable_map_iff]
    rfl
  rw [h1, integrable_withDensity_iff_integrable_smul' hρ
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg _))]

/- English proof (translation)
Establish `h0 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 1`. Use `(intervalIntegral.intervalIntegrable_rpow' hr).congr ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Set.uIoc_of_le zero_le_one]`. Simplify using `[abs_of_pos hx.1]`.

Establish `h1 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume (-1) 0`. Rewrite using `[IntervalIntegrable.iff_comp_neg]`. Simplify using `only [abs_neg, neg_neg, neg_zero]`. Conclude with `h0.symm`. Establish `h2` using `h1.trans h0`.

Conclude with `(intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 h2`.
-/
theorem integrableOn_abs_rpow {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun x : ℝ => |x| ^ r) (Icc (-1) 1) volume := by
  have h0 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 1 := by
    refine (intervalIntegral.intervalIntegrable_rpow' hr).congr ?_
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    simp [abs_of_pos hx.1]
  have h1 : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simp only [abs_neg, neg_neg, neg_zero]
    exact h0.symm
  have h2 := h1.trans h0
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 h2

/- English proof (translation)
Introduce `f e s hs`. Set `g : ℝ → ℂ` to `fun x => f x * ((if e ∧ x < 0 then -1 else 1) * ((|x| : ℝ) : ℂ) ^ s)`. Establish `key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume`. Establish `hsgn : Measurable fun x : ℝ => (if e ∧ x < 0 then (-1 : ℂ) else 1)`. Use `Measurable.ite ?_ measurable_const measurable_const` and prove the remaining obligations.

Consider the cases of `e`. Simplify using the standard rewrite rules. Simplify using `using measurableSet_lt measurable_id measurable_const`. Establish `hpow : Measurable fun x : ℝ => ((|x| : ℝ) : ℂ) ^ s` using `(Complex.measurable_ofReal.comp measurable_abs).pow_const s`. Establish `hmeas : AEStronglyMeasurable (fun x : ℝ => |x|⁻¹ • g x) volume` using `(measurable_abs.inv.smul (f.continuous.measurable.mul (hsgn.mul hpow))).aestronglyMeasurable`.

Establish `hbound : ∀ x : ℝ, ‖|x|⁻¹ • g x‖ ≤ ‖f x‖ * |x| ^ (s.re - 1)`. Introduce `x`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using `only [abs_zero, inv_zero, zero_smul, norm_zero]`. Conclude with `mul_nonneg (norm_nonneg _) (Real.rpow_nonneg le_rfl _)`.

Establish `hax : 0 < |x|` using `abs_pos.2 hx`. Apply the tactic sequence `have hsg : ‖(if e ∧ x < 0 then (-1 : ℂ) else 1)‖ = 1 := by split_ifs <;> simp`. Simplify using `only [g]`. Rewrite using `[norm_smul, norm_mul, norm_mul, hsg, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hax, Real.norm_eq_abs, abs_inv, abs_abs, Real.rpow_sub_one hax.ne']`. Conclude with `le_of_eq (by ring)`.

Establish `hC` using `SchwartzMap.norm_le_seminorm ℝ f`. Establish `hr : -1 < s.re - 1` using `by linarith`. Establish `hI : IntegrableOn (fun x : ℝ => |x|⁻¹ • g x) (Icc (-1) 1) volume`. Use `Integrable.mono' ((integrableOn_abs_rpow hr).const_mul ((SchwartzMap.seminorm ℝ 0 0) f)) hmeas.restrict ?_` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun x => (hbound x).trans ?_` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg (abs_nonneg x) _)`. Establish `hO : IntegrableOn (fun x : ℝ => |x|⁻¹ • g x) (Icc (-1) 1)ᶜ volume`. Use `Integrable.mono' (f.integrable_pow_mul volume ⌈s.re⌉₊).integrableOn hmeas.restrict ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Icc.compl).2 (Filter.Eventually.of_forall fun x hx => ?_)` and prove the remaining obligations. Establish `h1 : 1 ≤ |x|`.

Simplify using `only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx`. Break down `hx with hx | hx` into its components or cases. Rewrite using `[abs_of_neg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[abs_of_pos (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(hbound x).trans ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, mul_comm]`. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast]`.

Conclude with `Real.rpow_le_rpow_of_exponent_le h1 (by linarith [Nat.le_ceil s.re])`. Establish `hU` using `hI.union hO`. Rewrite `hU` using `[Set.union_compl_self, integrableOn_univ]`. Then use the resulting hypothesis. Conclude with `(integrable_mulR_iff g).2 key`.
-/
theorem tateInt : LR.C.TateInt := by
  intro f e s hs
  let g : ℝ → ℂ := fun x => f x * ((if e ∧ x < 0 then -1 else 1) * ((|x| : ℝ) : ℂ) ^ s)
  have key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
    have hsgn : Measurable fun x : ℝ => (if e ∧ x < 0 then (-1 : ℂ) else 1) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      cases e
      · simp
      · simpa using measurableSet_lt measurable_id measurable_const
    have hpow : Measurable fun x : ℝ => ((|x| : ℝ) : ℂ) ^ s :=
      (Complex.measurable_ofReal.comp measurable_abs).pow_const s
    have hmeas : AEStronglyMeasurable (fun x : ℝ => |x|⁻¹ • g x) volume :=
      (measurable_abs.inv.smul (f.continuous.measurable.mul (hsgn.mul hpow))).aestronglyMeasurable
    have hbound : ∀ x : ℝ, ‖|x|⁻¹ • g x‖ ≤ ‖f x‖ * |x| ^ (s.re - 1) := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp only [abs_zero, inv_zero, zero_smul, norm_zero]
        exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg le_rfl _)
      · have hax : 0 < |x| := abs_pos.2 hx
        have hsg : ‖(if e ∧ x < 0 then (-1 : ℂ) else 1)‖ = 1 := by split_ifs <;> simp
        simp only [g]
        rw [norm_smul, norm_mul, norm_mul, hsg, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hax,
          Real.norm_eq_abs, abs_inv, abs_abs, Real.rpow_sub_one hax.ne']
        exact le_of_eq (by ring)
    have hC := SchwartzMap.norm_le_seminorm ℝ f
    have hr : -1 < s.re - 1 := by linarith
    have hI : IntegrableOn (fun x : ℝ => |x|⁻¹ • g x) (Icc (-1) 1) volume := by
      refine Integrable.mono' ((integrableOn_abs_rpow hr).const_mul ((SchwartzMap.seminorm ℝ 0 0) f)) hmeas.restrict ?_
      refine Filter.Eventually.of_forall fun x => (hbound x).trans ?_
      exact mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg (abs_nonneg x) _)
    have hO : IntegrableOn (fun x : ℝ => |x|⁻¹ • g x) (Icc (-1) 1)ᶜ volume := by
      refine Integrable.mono' (f.integrable_pow_mul volume ⌈s.re⌉₊).integrableOn hmeas.restrict ?_
      refine (ae_restrict_iff' measurableSet_Icc.compl).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have h1 : 1 ≤ |x| := by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]
          linarith
        · rw [abs_of_pos (by linarith)]
          linarith
      refine (hbound x).trans ?_
      rw [Real.norm_eq_abs, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith [Nat.le_ceil s.re])
    have hU := hI.union hO
    rwa [Set.union_compl_self, integrableOn_univ] at hU
  exact (integrable_mulR_iff g).2 key

end GlobalTheory.CompanionTheory.RealTateConv
