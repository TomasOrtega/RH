import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeTheorem

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

/- English proof (translation)
Simplify using `[toIdele_apply]`.
-/
theorem one_toIdele_eq_cpow (x : IdeleGroup K) :
    ((1 : HeckeCharacter K).toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) * I) := by
  simp [toIdele_apply]

/- English proof (translation)
Rewrite using `[discrNormConductor, conductor_eq_top_of_forall one_toIdele_eq_cpow, Ideal.absNorm_top]`. Simplify using the standard rewrite rules.
-/
theorem discrNormConductor_one : (1 : HeckeCharacter K).discrNormConductor = |(discr K : ℝ)| := by
  rw [discrNormConductor, conductor_eq_top_of_forall one_toIdele_eq_cpow, Ideal.absNorm_top]
  simp

open Classical in

/- English proof (translation)
Establish `h : ∀ w, (1 : HeckeCharacter K).infiniteGamma w s = if w.IsReal then Gammaℝ s else Gammaℂ s` using `fun w ↦ by`. Rewrite using `[infiniteGamma, infiniteTau_of_forall one_toIdele_eq_cpow, infiniteWeight_of_forall one_toIdele_eq_cpow]`. Simplify using the standard rewrite rules. Rewrite using `[gammaFactor, Finset.prod_congr rfl fun w _ ↦ h w, prod_eq_prod_mul_prod]`. Establish `h1 : ∀ w : {w : InfinitePlace K // IsReal w}, (if w.1.IsReal then Gammaℝ s else Gammaℂ s) = Gammaℝ s` using `fun w ↦ if_pos w.2`.

Establish `h2 : ∀ w : {w : InfinitePlace K // IsComplex w}, (if w.1.IsReal then Gammaℝ s else Gammaℂ s) = Gammaℂ s` using `fun w ↦ if_neg (not_isReal_iff_isComplex.2 w.2)`. Simplify using `only [h1, h2, Finset.prod_const, Finset.card_univ]`.
-/
theorem gammaFactor_one (s : ℂ) :
    (1 : HeckeCharacter K).gammaFactor s =
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  have h : ∀ w, (1 : HeckeCharacter K).infiniteGamma w s =
      if w.IsReal then Gammaℝ s else Gammaℂ s := fun w ↦ by
    rw [infiniteGamma, infiniteTau_of_forall one_toIdele_eq_cpow,
      infiniteWeight_of_forall one_toIdele_eq_cpow]
    simp
  rw [gammaFactor, Finset.prod_congr rfl fun w _ ↦ h w, prod_eq_prod_mul_prod]
  have h1 : ∀ w : {w : InfinitePlace K // IsReal w},
      (if w.1.IsReal then Gammaℝ s else Gammaℂ s) = Gammaℝ s := fun w ↦ if_pos w.2
  have h2 : ∀ w : {w : InfinitePlace K // IsComplex w},
      (if w.1.IsReal then Gammaℝ s else Gammaℂ s) = Gammaℂ s := fun w ↦
    if_neg (not_isReal_iff_isComplex.2 w.2)
  simp only [h1, h2, Finset.prod_const, Finset.card_univ]

end HeckeCharacter

open HeckeCharacter

variable (K)

def completedDedekindZeta (s : ℂ) : ℂ := (1 : HeckeCharacter K).completedLFunction s

/- English proof (translation)
The claim follows from `differentiableAt_completedLFunction_of_forall (one_toIdele_eq_cpow (K := K)) (by simpa using hs₀) (by simpa using hs₁)`.
-/
theorem differentiableAt_completedDedekindZeta {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (completedDedekindZeta K) s :=
  differentiableAt_completedLFunction_of_forall (one_toIdele_eq_cpow (K := K)) (by simpa using hs₀)
    (by simpa using hs₁)

/- English proof (translation)
Establish `h` using `tendsto_mul_completedLFunction_neg_of_forall (one_toIdele_eq_cpow (K := K))`. Simplify using `only [ofReal_zero, zero_mul, neg_zero, add_zero, zero_div, cpow_zero, mul_one] at h`. Conclude with `h`.
-/
theorem tendsto_mul_completedDedekindZeta_zero_volume :
    Tendsto (fun s ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-(((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹))) := by
  have h := tendsto_mul_completedLFunction_neg_of_forall (one_toIdele_eq_cpow (K := K))
  simp only [ofReal_zero, zero_mul, neg_zero, add_zero, zero_div, cpow_zero, mul_one] at h
  exact h

/- English proof (translation)
Establish `h` using `completedLFunction_eq_rootNumber_mul_of_forall (one_toIdele_eq_cpow (K := K)) (s := s) (by simpa using hs₀) (by simpa using hs₁)`. Rewrite `h` using `[inv_one]`. Then use the resulting hypothesis.
-/
theorem completedDedekindZeta_eq_rootNumber_mul {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedDedekindZeta K s =
      (1 : HeckeCharacter K).rootNumber * completedDedekindZeta K (1 - s) := by
  have h := completedLFunction_eq_rootNumber_mul_of_forall (one_toIdele_eq_cpow (K := K)) (s := s)
    (by simpa using hs₀) (by simpa using hs₁)
  rwa [inv_one] at h

/- English proof (translation)
Use `tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs ↦ ?_⟩` and prove the remaining obligations. Conclude with `((continuous_const.sub continuous_id).tendsto' 1 0 (by simp)).mono_left nhdsWithin_le_nhds`. Conclude with `sub_ne_zero.2 (Ne.symm hs)`.
-/
theorem tendsto_one_sub_nhdsNE_one : Tendsto (fun s : ℂ ↦ 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs ↦ ?_⟩
  · exact ((continuous_const.sub continuous_id).tendsto' 1 0 (by simp)).mono_left nhdsWithin_le_nhds
  · exact sub_ne_zero.2 (Ne.symm hs)

/- English proof (translation)
Establish `h` using `((tendsto_mul_completedDedekindZeta_zero_volume K).comp tendsto_one_sub_nhdsNE_one).const_mul (-(1 : HeckeCharacter K).rootNumber)`. Rewrite `h` using `[show -(1 : HeckeCharacter K).rootNumber * -(((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹) = (1 : HeckeCharacter K).rootNumber * (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹) by ring]`. Use `h.congr' ?_` and prove the remaining obligations. Establish `h0 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 0` using `eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds one_ne_zero)`. Use `filter_upwards [h0, self_mem_nhdsWithin] with s hs₀ hs₁`.

Rewrite using `[Function.comp_apply, completedDedekindZeta_eq_rootNumber_mul K hs₀ hs₁]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_sub_one_mul_completedDedekindZeta_rootNumber :
    Tendsto (fun s ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 ((1 : HeckeCharacter K).rootNumber *
        (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹))) := by
  have h := ((tendsto_mul_completedDedekindZeta_zero_volume K).comp
    tendsto_one_sub_nhdsNE_one).const_mul (-(1 : HeckeCharacter K).rootNumber)
  rw [show -(1 : HeckeCharacter K).rootNumber * -(((normOneClassMeasure K univ).toReal : ℂ) *
    ((π : ℂ) ^ nrComplexPlaces K)⁻¹) = (1 : HeckeCharacter K).rootNumber *
      (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹) by ring] at h
  refine h.congr' ?_
  have h0 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds one_ne_zero)
  filter_upwards [h0, self_mem_nhdsWithin] with s hs₀ hs₁
  rw [Function.comp_apply, completedDedekindZeta_eq_rootNumber_mul K hs₀ hs₁]
  ring

/- English proof (translation)
Establish `h` using `(1 : HeckeCharacter K).differentiable_cpow_mul_gammaFactor_inv`. Simplify using `only [discrNormConductor_one, gammaFactor_one] at h`. Conclude with `h`.
-/
theorem differentiable_discr_cpow_mul_gamma_inv :
    Differentiable ℂ fun s : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) *
      (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)⁻¹ := by
  have h := (1 : HeckeCharacter K).differentiable_cpow_mul_gammaFactor_inv
  simp only [discrNormConductor_one, gammaFactor_one] at h
  exact h

def normalizedDedekindZeta (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) *
    (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)⁻¹ * completedDedekindZeta K s

/- English proof (translation)
Establish `h` using `(1 : HeckeCharacter K).LFunction_eq_mul_completedLFunction hs`. Rewrite `h` using `[LFunction_one, discrNormConductor_one, gammaFactor_one]`. Conclude with `h.symm`.
-/
theorem normalizedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) : normalizedDedekindZeta K s = dedekindZeta K s := by
  have h := (1 : HeckeCharacter K).LFunction_eq_mul_completedLFunction hs
  rw [LFunction_one, discrNormConductor_one, gammaFactor_one] at h
  exact h.symm

/- English proof (translation)
Establish `hH` using `((differentiable_discr_cpow_mul_gamma_inv K).continuous.tendsto 1).mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))`. Use `(hH.mul (tendsto_sub_one_mul_completedDedekindZeta_rootNumber K)).congr fun s ↦ ?_` and prove the remaining obligations. Simplify using `only [normalizedDedekindZeta]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem residue_normalizedDedekindZeta_at_one :
    Tendsto (fun s ↦ (s - 1) * normalizedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-((1 : ℂ) / 2)) *
        (Gammaℝ 1 ^ nrRealPlaces K * Gammaℂ 1 ^ nrComplexPlaces K)⁻¹ *
        ((1 : HeckeCharacter K).rootNumber *
        (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹)))) := by
  have hH := ((differentiable_discr_cpow_mul_gamma_inv K).continuous.tendsto 1).mono_left
    (nhdsWithin_le_nhds (s := {1}ᶜ))
  refine (hH.mul (tendsto_sub_one_mul_completedDedekindZeta_rootNumber K)).congr fun s ↦ ?_
  simp only [normalizedDedekindZeta]
  ring

/- English proof (translation)
Use `tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun s (hs : 1 < s) ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [mem_compl_iff, mem_singleton_iff]`. Conclude with `hs.ne'` after adjusting the coercions.
-/
theorem tendsto_ofReal_nhdsGT_one : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto' 1 1 (by simp)).mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun s (hs : 1 < s) ↦ ?_⟩
  simp only [mem_compl_iff, mem_singleton_iff]
  exact_mod_cast hs.ne'

/- English proof (translation)
Establish `hres : _ = (dedekindZeta_residue K : ℂ)` using `tendsto_nhds_unique ((residue_normalizedDedekindZeta_at_one K).comp tendsto_ofReal_nhdsGT_one) ((tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' (by filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)`. Rewrite using `[Function.comp_apply, normalizedDedekindZeta_eq K (by simpa using hs)]))`. Rewrite `hres` using `[Gammaℝ_one, Gammaℂ_one, one_pow, one_mul]`. Establish `ha : 0 ≤ |(discr K : ℝ)|` using `abs_nonneg _`. Establish `hπ : (π : ℂ) ≠ 0` using `ofReal_ne_zero.2 Real.pi_ne_zero`.

Rewrite using `[← hres, ofReal_mul, ofReal_cpow ha]`. Use `push_cast`. Simplify using `only [one_div, inv_pow, inv_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem rootNumber_mul_volume :
    (1 : HeckeCharacter K).rootNumber *
      ((|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal : ℝ) : ℂ) =
      (dedekindZeta_residue K : ℂ) := by
  have hres : _ = (dedekindZeta_residue K : ℂ) := tendsto_nhds_unique
    ((residue_normalizedDedekindZeta_at_one K).comp tendsto_ofReal_nhdsGT_one)
    ((tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' (by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      rw [Function.comp_apply, normalizedDedekindZeta_eq K (by simpa using hs)]))
  rw [Gammaℝ_one, Gammaℂ_one, one_pow, one_mul] at hres
  have ha : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [← hres, ofReal_mul, ofReal_cpow ha]
  push_cast
  simp only [one_div, inv_pow, inv_inv]
  field_simp

/- English proof (translation)
Establish `h2` using `(1 : HeckeCharacter K).rootNumber_mul_rootNumber_inv`. Rewrite `h2` using `[inv_one]`. Establish `h` using `rootNumber_mul_volume K`. Establish `ha : 0 < |(discr K : ℝ)|` using `abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))`. Establish `hv : 0 < (normOneClassMeasure K univ).toReal` using `lt_of_le_of_ne ENNReal.toReal_nonneg (normOneClassMeasure_univ_toReal_ne_zero K).symm`.

Establish `hb : 0 < |(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal` using `mul_pos (Real.rpow_pos_of_pos ha _) hv`. Establish `hW : (1 : HeckeCharacter K).rootNumber = ((dedekindZeta_residue K / (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal) : ℝ) : ℂ)`. Rewrite using `[ofReal_div, ← h, mul_div_cancel_right₀ _ (ofReal_ne_zero.2 hb.ne')]`. Establish `ht : 0 < dedekindZeta_residue K / (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal)` using `div_pos (dedekindZeta_residue_pos K) hb`. Rewrite `h2` using `[hW, ← ofReal_mul, ofReal_eq_one]`.

Rewrite using `[hW, show dedekindZeta_residue K / (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal) = 1 by nlinarith, ofReal_one]`.
-/
theorem HeckeCharacter.rootNumber_one : (1 : HeckeCharacter K).rootNumber = 1 := by
  have h2 := (1 : HeckeCharacter K).rootNumber_mul_rootNumber_inv
  rw [inv_one] at h2
  have h := rootNumber_mul_volume K
  have ha : 0 < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have hv : 0 < (normOneClassMeasure K univ).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (normOneClassMeasure_univ_toReal_ne_zero K).symm
  have hb : 0 < |(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal :=
    mul_pos (Real.rpow_pos_of_pos ha _) hv
  have hW : (1 : HeckeCharacter K).rootNumber = ((dedekindZeta_residue K /
      (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal) : ℝ) : ℂ) := by
    rw [ofReal_div, ← h, mul_div_cancel_right₀ _ (ofReal_ne_zero.2 hb.ne')]
  have ht : 0 < dedekindZeta_residue K /
      (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal) :=
    div_pos (dedekindZeta_residue_pos K) hb
  rw [hW, ← ofReal_mul, ofReal_eq_one] at h2
  rw [hW, show dedekindZeta_residue K /
      (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal) = 1 by nlinarith,
    ofReal_one]

/- English proof (translation)
Establish `h` using `rootNumber_mul_volume K`. Rewrite `h` using `[rootNumber_one, one_mul, ofReal_inj]`. Establish `ha : 0 < |(discr K : ℝ)|` using `abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))`. Rewrite using `[← h, Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add ha]`. Evaluate the numerical expressions.
-/
theorem normOneClassMeasure_univ_toReal_eq :
    (normOneClassMeasure K univ).toReal = Real.sqrt |(discr K : ℝ)| * dedekindZeta_residue K := by
  have h := rootNumber_mul_volume K
  rw [rootNumber_one, one_mul, ofReal_inj] at h
  have ha : 0 < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  rw [← h, Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add ha]
  norm_num

open NumberField.Units in

/- English proof (translation)
Rewrite using `[normOneClassMeasure_univ_toReal_eq, dedekindZeta_residue_def]`. Establish `h1 : 0 < Real.sqrt |(discr K : ℝ)|` using `Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))`. Establish `h2 : (0 : ℝ) < torsionOrder K` using `Nat.cast_pos.2 (torsionOrder_pos K)`. Clear the denominators using the available nonvanishing facts.
-/
theorem normOneClassMeasure_univ_toReal_eq_classNumber :
    (normOneClassMeasure K univ).toReal = 2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K *
      regulator K * classNumber K / torsionOrder K := by
  rw [normOneClassMeasure_univ_toReal_eq, dedekindZeta_residue_def]
  have h1 : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  have h2 : (0 : ℝ) < torsionOrder K := Nat.cast_pos.2 (torsionOrder_pos K)
  field_simp

/- English proof (translation)
Rewrite using `[completedDedekindZeta_eq_rootNumber_mul K hs₀ hs₁, rootNumber_one, one_mul]`.
-/
theorem completedDedekindZeta_one_sub {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  rw [completedDedekindZeta_eq_rootNumber_mul K hs₀ hs₁, rootNumber_one, one_mul]

/- English proof (translation)
Establish `h` using `tendsto_mul_completedDedekindZeta_zero_volume K`. Rewrite `h` using `[normOneClassMeasure_univ_toReal_eq]`. Then use the resulting hypothesis.
-/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-(((Real.sqrt |(discr K : ℝ)| * dedekindZeta_residue K : ℝ) : ℂ) *
        ((π : ℂ) ^ nrComplexPlaces K)⁻¹))) := by
  have h := tendsto_mul_completedDedekindZeta_zero_volume K
  rwa [normOneClassMeasure_univ_toReal_eq] at h

end

end GroundTheory.Global
