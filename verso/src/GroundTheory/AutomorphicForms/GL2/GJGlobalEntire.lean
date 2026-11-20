import Mathlib

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

variable {J J' : ℝ → ℂ}

/- English proof (translation)
Rewrite using `[locallyIntegrableOn_iff (isOpen_Ioi.isLocallyClosed)]`. Introduce `k hk hkc`. Conclude with `((hJ.mono hk).integrableOn_compact hkc).indicator measurableSet_Ici`.
-/
theorem locallyIntegrableOn_indicator_Ici (hJ : ContinuousOn J (Ioi 0)) :
    LocallyIntegrableOn ((Ici (1 : ℝ)).indicator J) (Ioi 0) := by
  rw [locallyIntegrableOn_iff (isOpen_Ioi.isLocallyClosed)]
  intro k hk hkc
  exact ((hJ.mono hk).integrableOn_compact hkc).indicator measurableSet_Ici

/- English proof (translation)
Rewrite using `[locallyIntegrableOn_iff (isOpen_Ioi.isLocallyClosed)]`. Introduce `k hk hkc`. Conclude with `((hJ.mono hk).integrableOn_compact hkc).indicator measurableSet_Ioi`.
-/
theorem locallyIntegrableOn_indicator_Ioi (hJ : ContinuousOn J (Ioi 0)) :
    LocallyIntegrableOn ((Ioi (1 : ℝ)).indicator J) (Ioi 0) := by
  rw [locallyIntegrableOn_iff (isOpen_Ioi.isLocallyClosed)]
  intro k hk hkc
  exact ((hJ.mono hk).integrableOn_compact hkc).indicator measurableSet_Ioi

/- English proof (translation)
Use `EventuallyEq.trans_isBigO ?_ h` and prove the remaining obligations. Use `filter_upwards [hA] with t ht`. Conclude with `indicator_of_mem ht J`.
-/
theorem isBigO_indicator_atTop {A : Set ℝ} (hA : A ∈ atTop) {a : ℝ}
    (h : J =O[atTop] (· ^ (-a))) : A.indicator J =O[atTop] (· ^ (-a)) := by
  refine EventuallyEq.trans_isBigO ?_ h
  filter_upwards [hA] with t ht
  exact indicator_of_mem ht J

/- English proof (translation)
Use `EventuallyEq.trans_isBigO (f₂ := fun _ => (0 : ℂ)) ?_ (isBigO_zero _ _)` and prove the remaining obligations. Use `filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht`. Conclude with `indicator_of_notMem (fun h => absurd (hA h) (not_le.2 ht.2)) J`.
-/
theorem isBigO_indicator_nhdsGT {A : Set ℝ} (hA : A ⊆ Ici 1) (b : ℝ) :
    A.indicator J =O[𝓝[>] 0] (· ^ (-b)) := by
  refine EventuallyEq.trans_isBigO (f₂ := fun _ => (0 : ℂ)) ?_ (isBigO_zero _ _)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact indicator_of_notMem (fun h => absurd (hA h) (not_le.2 ht.2)) J

/- English proof (translation)
Introduce `w`. Conclude with `mellin_differentiableAt_of_isBigO_rpow hloc (isBigO_indicator_atTop hAt (hd (w.re + 1))) (lt_add_one _) (isBigO_indicator_nhdsGT hA (w.re - 1)) (sub_one_lt _)`.
-/
theorem differentiable_mellin_indicator {A : Set ℝ} (hA : A ⊆ Ici 1) (hAt : A ∈ atTop)
    (hloc : LocallyIntegrableOn (A.indicator J) (Ioi 0))
    (hd : ∀ a : ℝ, J =O[atTop] (· ^ (-a))) : Differentiable ℂ (mellin (A.indicator J)) := by
  intro w
  exact mellin_differentiableAt_of_isBigO_rpow hloc (isBigO_indicator_atTop hAt (hd (w.re + 1)))
    (lt_add_one _) (isBigO_indicator_nhdsGT hA (w.re - 1)) (sub_one_lt _)

/- English proof (translation)
Establish `: (fun t : ℝ => (t : ℂ) ^ (w - 1) • A.indicator J t) = A.indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) • J t)`. Use function extensionality and compare the values at `t`. Apply the tactic sequence `by_cases ht : t ∈ A <;> simp [ht]`. Unfold `MellinConvergent`. Rewrite using `[this]`.

Conclude with `hc.indicator hA`.
-/
theorem mellinConvergent_indicator {A : Set ℝ} (hA : MeasurableSet A) {w : ℂ}
    (hc : MellinConvergent J w) : MellinConvergent (A.indicator J) w := by
  have : (fun t : ℝ => (t : ℂ) ^ (w - 1) • A.indicator J t) =
      A.indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) • J t) := by
    funext t
    by_cases ht : t ∈ A <;> simp [ht]
  unfold MellinConvergent
  rw [this]
  exact hc.indicator hA

/- English proof (translation)
Establish `h1` using `mellinConvergent_indicator (J := J) (A := Ici 1) measurableSet_Ici hc`. Establish `h2` using `mellinConvergent_indicator (J := J) (A := Iio 1) measurableSet_Iio hc`. Unfold `mellin`. Rewrite using `[← integral_add h1 h2]`. Use `setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[← smul_add]`. Use `congr 1`. Use `Set.indicator_self_add_compl (Ici (1 : ℝ)) J` as an intermediate fact. Rewrite `this` using `[compl_Ici]`. Conclude with `(congrFun this t).symm`.
-/
theorem mellin_eq_add_of_convergent {w : ℂ} (hc : MellinConvergent J w) :
    mellin J w = mellin ((Ici (1 : ℝ)).indicator J) w + mellin ((Iio (1 : ℝ)).indicator J) w := by
  have h1 := mellinConvergent_indicator (J := J) (A := Ici 1) measurableSet_Ici hc
  have h2 := mellinConvergent_indicator (J := J) (A := Iio 1) measurableSet_Iio hc
  unfold mellin
  rw [← integral_add h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← smul_add]
  congr 1
  have := Set.indicator_self_add_compl (Ici (1 : ℝ)) J
  rw [compl_Ici] at this
  exact (congrFun this t).symm

/- English proof (translation)
Establish `e : mellin ((Iio (1 : ℝ)).indicator J) w = mellin (fun t : ℝ => (t : ℂ) ^ (-(κ : ℂ)) • (fun u : ℝ => (Ioi (1 : ℝ)).indicator J' u⁻¹) t) w`. Unfold `mellin`. Use `setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Use `congr 1`.

Distinguish the cases in `h1 : t < 1`. Establish `: 1 < t⁻¹` using `one_lt_inv₀ ht |>.2 h1`. Rewrite using `[indicator_of_mem (show t ∈ Iio 1 from h1), indicator_of_mem (show t⁻¹ ∈ Ioi 1 from this), hsym t ht]`. Establish `: ¬ 1 < t⁻¹` using `fun h => h1 ((one_lt_inv₀ ht).1 h)`. Rewrite using `[indicator_of_notMem (show t ∉ Iio 1 from h1), indicator_of_notMem (show t⁻¹ ∉ Ioi 1 from this), mul_zero]`.

Rewrite using `[e, mellin_cpow_smul, mellin_comp_inv]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mellin_indicator_Iio_eq {κ : ℝ} (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹)
    (w : ℂ) :
    mellin ((Iio (1 : ℝ)).indicator J) w = mellin ((Ioi (1 : ℝ)).indicator J') (κ - w) := by
  have e : mellin ((Iio (1 : ℝ)).indicator J) w =
      mellin (fun t : ℝ => (t : ℂ) ^ (-(κ : ℂ)) • (fun u : ℝ => (Ioi (1 : ℝ)).indicator J' u⁻¹) t) w := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [smul_eq_mul]
    congr 1
    by_cases h1 : t < 1
    · have : 1 < t⁻¹ := one_lt_inv₀ ht |>.2 h1
      rw [indicator_of_mem (show t ∈ Iio 1 from h1), indicator_of_mem (show t⁻¹ ∈ Ioi 1 from this),
        hsym t ht]
    · have : ¬ 1 < t⁻¹ := fun h => h1 ((one_lt_inv₀ ht).1 h)
      rw [indicator_of_notMem (show t ∉ Iio 1 from h1),
        indicator_of_notMem (show t⁻¹ ∉ Ioi 1 from this), mul_zero]
  rw [e, mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

/- English proof (translation)
Unfold `mellin`. Use `setIntegral_congr_ae measurableSet_Ioi ?_` and prove the remaining obligations. Establish `h : ∀ᵐ t : ℝ, t ≠ 1`. Simplify using `[ae_iff, measure_singleton]`. Use `filter_upwards [h] with t ht _`.

Use `congr 1`. Distinguish the cases in `h1 : 1 < t`. Rewrite using `[indicator_of_mem (show t ∈ Ici 1 from h1.le), indicator_of_mem (show t ∈ Ioi 1 from h1)]`. Establish `h2 : ¬ 1 ≤ t` using `fun h => h1 (lt_of_le_of_ne h (Ne.symm ht))`. Rewrite using `[indicator_of_notMem (show t ∉ Ici 1 from h2), indicator_of_notMem (show t ∉ Ioi 1 from h1)]`.
-/
theorem mellin_indicator_Ici_eq_Ioi (f : ℝ → ℂ) (w : ℂ) :
    mellin ((Ici (1 : ℝ)).indicator f) w = mellin ((Ioi (1 : ℝ)).indicator f) w := by
  unfold mellin
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  have h : ∀ᵐ t : ℝ, t ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h] with t ht _
  congr 1
  by_cases h1 : 1 < t
  · rw [indicator_of_mem (show t ∈ Ici 1 from h1.le), indicator_of_mem (show t ∈ Ioi 1 from h1)]
  · have h2 : ¬ 1 ≤ t := fun h => h1 (lt_of_le_of_ne h (Ne.symm ht))
    rw [indicator_of_notMem (show t ∉ Ici 1 from h2), indicator_of_notMem (show t ∉ Ioi 1 from h1)]

/- English proof (translation)
Introduce `t ht`. Establish `harg : (t : ℂ).arg ≠ Real.pi`. Rewrite using `[arg_ofReal_of_nonneg ht.le]`. Conclude with `Real.pi_pos.ne`. Rewrite using `[hsym t⁻¹ (inv_pos.2 ht), inv_inv, ← mul_assoc, ofReal_inv, inv_cpow _ _ harg, mul_inv_cancel₀ (cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 ht.ne'))), one_mul]`.
-/
theorem symm_of_symm {κ : ℝ} (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹) :
    ∀ t : ℝ, 0 < t → J' t = (t : ℂ) ^ (-(κ : ℂ)) * J t⁻¹ := by
  intro t ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  rw [hsym t⁻¹ (inv_pos.2 ht), inv_inv, ← mul_assoc, ofReal_inv, inv_cpow _ _ harg,
    mul_inv_cancel₀ (cpow_ne_zero_iff.2 (Or.inl (ofReal_ne_zero.2 ht.ne'))), one_mul]

/- English proof (translation)
Establish `hsym'` using `symm_of_symm hsym`. Establish `hIoi : Ioi (1 : ℝ) ∈ atTop` using `Ioi_mem_atTop 1`. Establish `hIci : Ici (1 : ℝ) ∈ atTop` using `Ici_mem_atTop 1`. Establish `d1` using `differentiable_mellin_indicator (subset_refl _) hIci (locallyIntegrableOn_indicator_Ici hJ) hdJ`. Establish `d2` using `differentiable_mellin_indicator Ioi_subset_Ici_self hIoi (locallyIntegrableOn_indicator_Ioi hJ') hdJ'`.

Establish `d1'` using `differentiable_mellin_indicator (subset_refl _) hIci (locallyIntegrableOn_indicator_Ici hJ') hdJ'`. Establish `d2'` using `differentiable_mellin_indicator Ioi_subset_Ici_self hIoi (locallyIntegrableOn_indicator_Ioi hJ) hdJ`. Use `⟨fun w => mellin ((Ici (1 : ℝ)).indicator J) w + mellin ((Ioi (1 : ℝ)).indicator J') (κ - w), fun w => mellin ((Ici (1 : ℝ)).indicator J') w + mellin ((Ioi (1 : ℝ)).indicator J) (κ - w), d1.add (d2.comp ((differentiable_const _).sub differentiable_id)), d1'.add (d2'.comp ((differ …` and prove the remaining obligations. Introduce `w hc`. Rewrite using `[mellin_eq_add_of_convergent hc, mellin_indicator_Iio_eq hsym]`.

Introduce `w hc`. Rewrite using `[mellin_eq_add_of_convergent hc, mellin_indicator_Iio_eq hsym']`. Introduce `w`. Simplify using `only [sub_sub_cancel]`. Rewrite using `[add_comm, mellin_indicator_Ici_eq_Ioi J, mellin_indicator_Ici_eq_Ioi J']`.
-/
theorem exists_entire_of_symm {κ : ℝ} (hJ : ContinuousOn J (Ioi 0)) (hJ' : ContinuousOn J' (Ioi 0))
    (hsym : ∀ t : ℝ, 0 < t → J t = (t : ℂ) ^ (-(κ : ℂ)) * J' t⁻¹)
    (hdJ : ∀ a : ℝ, J =O[atTop] (· ^ (-a))) (hdJ' : ∀ a : ℝ, J' =O[atTop] (· ^ (-a))) :
    ∃ Λ Λ' : ℂ → ℂ, Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ w, MellinConvergent J w → Λ w = mellin J w) ∧
      (∀ w, MellinConvergent J' w → Λ' w = mellin J' w) ∧ ∀ w, Λ w = Λ' (κ - w) := by
  have hsym' := symm_of_symm hsym
  have hIoi : Ioi (1 : ℝ) ∈ atTop := Ioi_mem_atTop 1
  have hIci : Ici (1 : ℝ) ∈ atTop := Ici_mem_atTop 1
  have d1 := differentiable_mellin_indicator (subset_refl _) hIci
    (locallyIntegrableOn_indicator_Ici hJ) hdJ
  have d2 := differentiable_mellin_indicator Ioi_subset_Ici_self hIoi
    (locallyIntegrableOn_indicator_Ioi hJ') hdJ'
  have d1' := differentiable_mellin_indicator (subset_refl _) hIci
    (locallyIntegrableOn_indicator_Ici hJ') hdJ'
  have d2' := differentiable_mellin_indicator Ioi_subset_Ici_self hIoi
    (locallyIntegrableOn_indicator_Ioi hJ) hdJ
  refine ⟨fun w => mellin ((Ici (1 : ℝ)).indicator J) w + mellin ((Ioi (1 : ℝ)).indicator J') (κ - w),
    fun w => mellin ((Ici (1 : ℝ)).indicator J') w + mellin ((Ioi (1 : ℝ)).indicator J) (κ - w),
    d1.add (d2.comp ((differentiable_const _).sub differentiable_id)),
    d1'.add (d2'.comp ((differentiable_const _).sub differentiable_id)), ?_, ?_, ?_⟩
  · intro w hc
    rw [mellin_eq_add_of_convergent hc, mellin_indicator_Iio_eq hsym]
  · intro w hc
    rw [mellin_eq_add_of_convergent hc, mellin_indicator_Iio_eq hsym']
  · intro w
    simp only [sub_sub_cancel]
    rw [add_comm, mellin_indicator_Ici_eq_Ioi J, mellin_indicator_Ici_eq_Ioi J']

end GJGlobal

end

end GroundTheory.Automorphic
