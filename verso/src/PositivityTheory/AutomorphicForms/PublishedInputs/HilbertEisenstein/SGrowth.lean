import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.EisensteinGrowth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

omit [IsTotallyReal F] in
/- English proof (translation)
Rewrite using `[Units.val_mul]`. Use extensionality with `i j`. Simplify using `[Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply]`.
-/
theorem scalar_mul_val (z : Ideles F) (h : GA F 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * h : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      (z : Ad F) • (h : Matrix (Fin 2) (Fin 2) (Ad F)) := by
  rw [Units.val_mul]
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply]

/- English proof (translation)
Break down `le_total x 1 with h | h` into its components or cases. Use `Real.rpow_le_one hx.le h (by norm_num : (0 : ℝ) ≤ 1 / 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 : ℝ) / 2 ≤ 1)` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rpow_half_le (x : ℝ) (hx : 0 < x) : x ^ ((1 : ℝ) / 2) ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx.le h (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 : ℝ) / 2 ≤ 1)
    rw [Real.rpow_one] at this
    linarith

/- English proof (translation)
Establish `h1 : x⁻¹ * x ^ ((1 : ℝ) / 2) = x⁻¹ ^ ((1 : ℝ) / 2)`. Rewrite using `[Real.inv_rpow hx.le, ← Real.rpow_neg_one x, ← Real.rpow_add hx, ← Real.rpow_neg hx.le]`. Evaluate the numerical expressions. Rewrite using `[h1]`. Conclude with `rpow_half_le _ (inv_pos.2 hx)`.
-/
theorem inv_mul_rpow_half_le (x : ℝ) (hx : 0 < x) : x⁻¹ * x ^ ((1 : ℝ) / 2) ≤ 1 + x⁻¹ := by
  have h1 : x⁻¹ * x ^ ((1 : ℝ) / 2) = x⁻¹ ^ ((1 : ℝ) / 2) := by
    rw [Real.inv_rpow hx.le, ← Real.rpow_neg_one x, ← Real.rpow_add hx, ← Real.rpow_neg hx.le]
    norm_num
  rw [h1]
  exact rpow_half_le _ (inv_pos.2 hx)

omit [IsTotallyReal F] in
/- English proof (translation)
Establish `hz : moduleSection (w0 F) t⁻¹ * u⁻¹ = (moduleSection (w0 F) t * u)⁻¹`. Rewrite using `[map_inv, mul_inv]`. Rewrite using `[hz, mul_inv_rev, ← map_inv, Units.val_mul]`. Use extensionality with `i`. Simplify using `[Matrix.GeneralLinearGroup.scalar, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem inv_scalar_mulVec (t : {r : ℝ // 0 < r}) (u : Ideles F) (h : GA F 2) (x : Fin 2 → Ad F) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * u) * h)⁻¹ : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ x =
      x ᵥ* (((moduleSection (w0 F) t⁻¹ * u⁻¹ : Ideles F) : Ad F) •
        ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose) := by
  have hz : moduleSection (w0 F) t⁻¹ * u⁻¹ = (moduleSection (w0 F) t * u)⁻¹ := by
    rw [map_inv, mul_inv]
  rw [hz, mul_inv_rev, ← map_inv, Units.val_mul]
  ext i
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.diagonal_apply]
  ring

end UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

open UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth in
/- English proof (translation)
Introduce `hP _ _ F _ _ _ ω c hyp g`. Take `⟨Cp, hCp⟩` from `hP F ω c hyp`. Take `⟨D, hD0, hD⟩` from `exists_D hyp`. Establish `hKc : IsCompact (Subtype.val '' closure (normOneFundamentalDomain F) : Set (Ideles F))` using `(isCompact_closure_normOneFundamentalDomain F).image continuous_subtype_val`. Take `⟨C1, N1, hC1, h1⟩` from `core D hD0 hD (norm_Phi_le c) hKc (((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F))`.

Take `⟨C2, N2, hC2, h2⟩` from `core D hD0 hD (norm_PhiH_le c) hKc.inv (((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose.map (pFin F))`. Take `⟨Ca, Na, hCa⟩` from `absD_mul_infGL_le g`. Take `⟨Cm, hCm0, hCm⟩` from `mn_bound g`. Take `⟨I, hI0, hI⟩ : ∃ I : ℝ, 0 ≤ I ∧ (normOneMeasure F (normOneFundamentalDomain F)).toReal * (∫⁻ t, ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) ∂posRealMeasure).toReal = I` from `⟨_, by positivity, rfl⟩`. Establish `hfin : ∀ y' : GL (Fin 2) (UpperTheory.V.TR.Rinf F), ((UpperTheory.V.TR.infGL F 2 y' : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = 1` using `fun y' => by`.

Use `congrArg (fun x : GL (Fin 2) (Af F) => (x : Matrix (Fin 2) (Fin 2) (Af F))) (UpperTheory.V.TR.pFin_infGL y')` as an intermediate fact. Conclude with `this`. Take `⟨A, hA⟩ : ∃ A : ℝ, (C1 * (1 + Cm) ^ N1 + ‖Cp‖ * C2 * (1 + Cm) ^ N2) * (1 + |Ca|) = A` from `⟨_, rfl⟩`. Use `⟨A * I, N1 + N2 + Na, fun y => ?_⟩` and prove the remaining obligations. Establish `hH1` using `one_le_height y`.

Take `⟨hCa1, hCa2⟩` from `hCa y`. Take `⟨hm1, hm2⟩` from `hCm y`. Establish `hhinv : (((g * UpperTheory.V.TR.infGL F 2 y)⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F)`. Rewrite using `[mul_inv_rev, ← map_inv, Units.val_mul, Matrix.map_mul, hfin, one_mul]`. Establish `hhT : ((g * UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose.map (pFin F) = ((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose.map (pFin F)`.

Rewrite using `[Matrix.transpose_map, Matrix.transpose_map, Units.val_mul, Matrix.map_mul, hfin, mul_one]`. Generalize the expression as in `UpperTheory.V.TR.height y = H at *`. Generalize the expression as in `g * UpperTheory.V.TR.infGL F 2 y = h at *`. Establish `hpos` using `absD_pos h`. Establish `hP1 : (1 + mn ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) ^ N1 ≤ (1 + Cm) ^ N1 * H ^ N1`.

Rewrite using `[← mul_pow]`. Use `gcongr`. Conclude with `add_nonneg zero_le_one (mn_nonneg _)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hP2 : (1 + mn ((h : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose) ^ N2 ≤ (1 + Cm) ^ N2 * H ^ N2`.

Rewrite using `[← mul_pow]`. Use `gcongr`. Conclude with `add_nonneg zero_le_one (mn_nonneg _)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hHa : (1 : ℝ) ≤ H ^ Na` using `one_le_pow₀ hH1`.

Establish `hQ1 : absD h ^ ((1 : ℝ) / 2) ≤ (1 + |Ca|) * H ^ Na`. Use `(rpow_half_le _ hpos).trans ?_` and prove the remaining obligations. Use `le_abs_self Ca` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hQ2 : (absD h)⁻¹ * absD h ^ ((1 : ℝ) / 2) ≤ (1 + |Ca|) * H ^ Na`.

Use `(inv_mul_rpow_half_le _ hpos).trans ?_` and prove the remaining obligations. Use `le_abs_self Ca` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Take `⟨Kb, hKb⟩ : ∃ Kb : ℝ, C1 * ((1 + Cm) ^ N1 * H ^ N1) * ((1 + |Ca|) * H ^ Na) + ‖Cp‖ * C2 * ((1 + Cm) ^ N2 * H ^ N2) * ((1 + |Ca|) * H ^ Na) = Kb` from `⟨_, rfl⟩`. Establish `hKb0 : 0 ≤ Kb` using `by rw [← hKb]; positivity`.

Establish `hb : ∀ t : {r : ℝ // 0 < r}, ∀ u ∈ normOneFundamentalDomain F, ‖eisInt ω (Phi c) h t u‖ ≤ Kb * min (t : ℝ) (t : ℝ)⁻¹`. Introduce `t u hu`. Establish `hu' : (u : Ideles F) ∈ (Subtype.val '' closure (normOneFundamentalDomain F) : Set (Ideles F))` using `⟨u, subset_closure hu, rfl⟩`. Establish `ht0 : (0 : ℝ) < t` using `t.2`. Establish `hnorm : ‖eisInt ω (Phi c) h t u‖ = ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * h)‖ * t * absD h ^ ((1 : ℝ) / 2)`.

Unfold `eisInt`. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_inv, norm_omega_eq_one hyp.fin, inv_one, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht0, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]`. Rewrite using `[hnorm]`. Establish `hQ0 : 0 ≤ absD h ^ ((1 : ℝ) / 2)` using `Real.rpow_nonneg hpos.le _`. Establish `hK1 : 0 ≤ (1 + |Ca|) * H ^ Na` using `by positivity`.

Break down `le_or_gt 1 (t : ℝ) with ht | ht` into its components or cases. Take `⟨hs, hle⟩` from `h1 u hu' t ht (h : Matrix (Fin 2) (Fin 2) (Ad F)) ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) (Units.mul_inv h) hhinv`. Establish `hθ : ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * h)‖ ≤ C1 * ((t : ℝ) ^ 2)⁻¹ * ((1 + Cm) ^ N1 * H ^ N1)`. Unfold `thetaS`. Simplify using `only [scalar_mul_val]`.

Use `(norm_tsum_le_tsum_norm hs).trans (hle.trans ?_)` and prove the remaining obligations. Use `gcongr`. Establish `hmin : min (t : ℝ) (t : ℝ)⁻¹ = (t : ℝ)⁻¹` using `min_eq_right ((inv_le_one_of_one_le₀ ht).trans ht)`. Rewrite using `[hmin]`. Combine the equalities or inequalities in the displayed calculation.

Clear the denominators using the available nonvanishing facts. Use `_ ≤ Kb * (t : ℝ)⁻¹ := by`. Rewrite using `[← hKb]`. Use `gcongr`. Conclude with `le_add_of_nonneg_right (by positivity)`.

Establish `hmin : min (t : ℝ) (t : ℝ)⁻¹ = t` using `min_eq_left (ht.le.trans ((one_le_inv₀ ht0).2 ht.le))`. Rewrite using `[hmin]`. Take `⟨_, hsum2, heq⟩` from `hCp (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * h)`. Establish `htc : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹` using `rfl`. Establish `htinv : (1 : ℝ) ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)`.

Rewrite using `[htc]`. Conclude with `(one_le_inv₀ ht0).2 ht.le`. Take `⟨hs2, hle2⟩` from `h2 ((u : Ideles F)⁻¹) (Set.inv_mem_inv.2 hu') t⁻¹ htinv ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose (h : Matrix (Fin 2) (Fin 2) (Ad F)).transpose (by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]) hhT`. Establish `hθT : ‖thetaT (PhiH c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * h)‖ ≤ C2 * (t : ℝ) ^ 2 * ((1 + Cm) ^ N2 * H ^ N2)`. Unfold `thetaT`.

Simplify using `only [inv_scalar_mulVec]`. Use `(norm_tsum_le_tsum_norm hs2).trans (hle2.trans ?_)` and prove the remaining obligations. Rewrite using `[htc, inv_pow, inv_inv]`. Use `gcongr`. Rewrite using `[heq, absD_scalar_mul t u h, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]`.

Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ ‖Cp‖ * C2 * ((1 + Cm) ^ N2 * H ^ N2) * ((1 + |Ca|) * H ^ Na) * t := by gcongr`. Use `_ ≤ Kb * t := by`. Rewrite using `[← hKb]`.

Use `gcongr`. Conclude with `le_add_of_nonneg_left (by positivity)`. Use `(norm_Eis_le ω (Phi c) h Kb hKb0 hb).trans ?_` and prove the remaining obligations. Rewrite using `[hI]`. Establish `hKbA : Kb ≤ A * H ^ (N1 + N2 + Na)`.

Rewrite using `[← hKb, ← hA]`. Establish `e1 : H ^ N1 * H ^ Na ≤ H ^ (N1 + N2 + Na)`. Rewrite using `[← pow_add]; exact pow_le_pow_right₀ hH1 (by omega)`. Establish `e2 : H ^ N2 * H ^ Na ≤ H ^ (N1 + N2 + Na)`. Rewrite using `[← pow_add]; exact pow_le_pow_right₀ hH1 (by omega)`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.HilbertEisensteinWeightOne.moderate_growth_holds : SPois → SInt → SSmooth → SGrowth := by
  intro hP _ _ F _ _ _ ω c hyp g
  obtain ⟨Cp, hCp⟩ := hP F ω c hyp
  obtain ⟨D, hD0, hD⟩ := exists_D hyp
  have hKc : IsCompact (Subtype.val '' closure (normOneFundamentalDomain F) : Set (Ideles F)) :=
    (isCompact_closure_normOneFundamentalDomain F).image continuous_subtype_val
  obtain ⟨C1, N1, hC1, h1⟩ := core D hD0 hD (norm_Phi_le c) hKc
    (((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F))
  obtain ⟨C2, N2, hC2, h2⟩ := core D hD0 hD (norm_PhiH_le c) hKc.inv
    (((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose.map (pFin F))
  obtain ⟨Ca, Na, hCa⟩ := absD_mul_infGL_le g
  obtain ⟨Cm, hCm0, hCm⟩ := mn_bound g
  obtain ⟨I, hI0, hI⟩ : ∃ I : ℝ, 0 ≤ I ∧ (normOneMeasure F (normOneFundamentalDomain F)).toReal *
      (∫⁻ t, ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) ∂posRealMeasure).toReal = I := ⟨_, by positivity, rfl⟩
  have hfin : ∀ y' : GL (Fin 2) (UpperTheory.V.TR.Rinf F),
      ((UpperTheory.V.TR.infGL F 2 y' : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = 1 := fun y' => by
    have := congrArg (fun x : GL (Fin 2) (Af F) => (x : Matrix (Fin 2) (Fin 2) (Af F))) (UpperTheory.V.TR.pFin_infGL y')
    exact this
  obtain ⟨A, hA⟩ : ∃ A : ℝ, (C1 * (1 + Cm) ^ N1 + ‖Cp‖ * C2 * (1 + Cm) ^ N2) * (1 + |Ca|) = A := ⟨_, rfl⟩
  refine ⟨A * I, N1 + N2 + Na, fun y => ?_⟩
  have hH1 := one_le_height y
  obtain ⟨hCa1, hCa2⟩ := hCa y
  obtain ⟨hm1, hm2⟩ := hCm y
  have hhinv : (((g * UpperTheory.V.TR.infGL F 2 y)⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) =
      ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) := by
    rw [mul_inv_rev, ← map_inv, Units.val_mul, Matrix.map_mul, hfin, one_mul]
  have hhT : ((g * UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose.map (pFin F) =
      ((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose.map (pFin F) := by
    rw [Matrix.transpose_map, Matrix.transpose_map, Units.val_mul, Matrix.map_mul, hfin, mul_one]
  generalize UpperTheory.V.TR.height y = H at *
  generalize g * UpperTheory.V.TR.infGL F 2 y = h at *
  have hpos := absD_pos h
  have hP1 : (1 + mn ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) ^ N1 ≤ (1 + Cm) ^ N1 * H ^ N1 := by
    rw [← mul_pow]
    gcongr
    · exact add_nonneg zero_le_one (mn_nonneg _)
    · nlinarith
  have hP2 : (1 + mn ((h : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose) ^ N2 ≤ (1 + Cm) ^ N2 * H ^ N2 := by
    rw [← mul_pow]
    gcongr
    · exact add_nonneg zero_le_one (mn_nonneg _)
    · nlinarith
  have hHa : (1 : ℝ) ≤ H ^ Na := one_le_pow₀ hH1
  have hQ1 : absD h ^ ((1 : ℝ) / 2) ≤ (1 + |Ca|) * H ^ Na := by
    refine (rpow_half_le _ hpos).trans ?_
    have := le_abs_self Ca
    nlinarith
  have hQ2 : (absD h)⁻¹ * absD h ^ ((1 : ℝ) / 2) ≤ (1 + |Ca|) * H ^ Na := by
    refine (inv_mul_rpow_half_le _ hpos).trans ?_
    have := le_abs_self Ca
    nlinarith
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, C1 * ((1 + Cm) ^ N1 * H ^ N1) * ((1 + |Ca|) * H ^ Na) +
      ‖Cp‖ * C2 * ((1 + Cm) ^ N2 * H ^ N2) * ((1 + |Ca|) * H ^ Na) = Kb := ⟨_, rfl⟩
  have hKb0 : 0 ≤ Kb := by rw [← hKb]; positivity
  have hb : ∀ t : {r : ℝ // 0 < r}, ∀ u ∈ normOneFundamentalDomain F,
      ‖eisInt ω (Phi c) h t u‖ ≤ Kb * min (t : ℝ) (t : ℝ)⁻¹ := by
    intro t u hu
    have hu' : (u : Ideles F) ∈ (Subtype.val '' closure (normOneFundamentalDomain F) : Set (Ideles F)) :=
      ⟨u, subset_closure hu, rfl⟩
    have ht0 : (0 : ℝ) < t := t.2
    have hnorm : ‖eisInt ω (Phi c) h t u‖ = ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2)
        (moduleSection (w0 F) t * (u : Ideles F)) * h)‖ * t * absD h ^ ((1 : ℝ) / 2) := by
      unfold eisInt
      rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_omega_eq_one hyp.fin, inv_one, mul_one,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht0,
        abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    rw [hnorm]
    have hQ0 : 0 ≤ absD h ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hpos.le _
    have hK1 : 0 ≤ (1 + |Ca|) * H ^ Na := by positivity
    rcases le_or_gt 1 (t : ℝ) with ht | ht
    · obtain ⟨hs, hle⟩ := h1 u hu' t ht (h : Matrix (Fin 2) (Fin 2) (Ad F))
        ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) (Units.mul_inv h) hhinv
      have hθ : ‖thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2)
          (moduleSection (w0 F) t * (u : Ideles F)) * h)‖ ≤
          C1 * ((t : ℝ) ^ 2)⁻¹ * ((1 + Cm) ^ N1 * H ^ N1) := by
        unfold thetaS
        simp only [scalar_mul_val]
        refine (norm_tsum_le_tsum_norm hs).trans (hle.trans ?_)
        gcongr
      have hmin : min (t : ℝ) (t : ℝ)⁻¹ = (t : ℝ)⁻¹ := min_eq_right ((inv_le_one_of_one_le₀ ht).trans ht)
      rw [hmin]
      calc _ ≤ C1 * ((t : ℝ) ^ 2)⁻¹ * ((1 + Cm) ^ N1 * H ^ N1) * t * ((1 + |Ca|) * H ^ Na) := by
            gcongr
        _ = C1 * ((1 + Cm) ^ N1 * H ^ N1) * ((1 + |Ca|) * H ^ Na) * (t : ℝ)⁻¹ := by
            field_simp
        _ ≤ Kb * (t : ℝ)⁻¹ := by
            rw [← hKb]
            gcongr
            exact le_add_of_nonneg_right (by positivity)
    · have hmin : min (t : ℝ) (t : ℝ)⁻¹ = t := min_eq_left (ht.le.trans ((one_le_inv₀ ht0).2 ht.le))
      rw [hmin]
      obtain ⟨_, hsum2, heq⟩ := hCp (Matrix.GeneralLinearGroup.scalar (Fin 2)
        (moduleSection (w0 F) t * (u : Ideles F)) * h)
      have htc : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := rfl
      have htinv : (1 : ℝ) ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) := by
        rw [htc]; exact (one_le_inv₀ ht0).2 ht.le
      obtain ⟨hs2, hle2⟩ := h2 ((u : Ideles F)⁻¹) (Set.inv_mem_inv.2 hu') t⁻¹ htinv
        ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).transpose
        (h : Matrix (Fin 2) (Fin 2) (Ad F)).transpose
        (by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]) hhT
      have hθT : ‖thetaT (PhiH c) (Matrix.GeneralLinearGroup.scalar (Fin 2)
          (moduleSection (w0 F) t * (u : Ideles F)) * h)‖ ≤
          C2 * (t : ℝ) ^ 2 * ((1 + Cm) ^ N2 * H ^ N2) := by
        unfold thetaT
        simp only [inv_scalar_mulVec]
        refine (norm_tsum_le_tsum_norm hs2).trans (hle2.trans ?_)
        rw [htc, inv_pow, inv_inv]
        gcongr
      rw [heq, absD_scalar_mul t u h, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      calc _ ≤ ‖Cp‖ * ((t : ℝ) ^ 2 * absD h)⁻¹ * (C2 * (t : ℝ) ^ 2 * ((1 + Cm) ^ N2 * H ^ N2)) * t *
            absD h ^ ((1 : ℝ) / 2) := by
            gcongr
        _ = ‖Cp‖ * C2 * ((1 + Cm) ^ N2 * H ^ N2) * ((absD h)⁻¹ * absD h ^ ((1 : ℝ) / 2)) * t := by
            field_simp
        _ ≤ ‖Cp‖ * C2 * ((1 + Cm) ^ N2 * H ^ N2) * ((1 + |Ca|) * H ^ Na) * t := by
            gcongr
        _ ≤ Kb * t := by
            rw [← hKb]
            gcongr
            exact le_add_of_nonneg_left (by positivity)
  refine (norm_Eis_le ω (Phi c) h Kb hKb0 hb).trans ?_
  rw [hI]
  have hKbA : Kb ≤ A * H ^ (N1 + N2 + Na) := by
    rw [← hKb, ← hA]
    have e1 : H ^ N1 * H ^ Na ≤ H ^ (N1 + N2 + Na) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hH1 (by omega)
    have e2 : H ^ N2 * H ^ Na ≤ H ^ (N1 + N2 + Na) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hH1 (by omega)
    calc _ = C1 * (1 + Cm) ^ N1 * (1 + |Ca|) * (H ^ N1 * H ^ Na) +
          ‖Cp‖ * C2 * (1 + Cm) ^ N2 * (1 + |Ca|) * (H ^ N2 * H ^ Na) := by ring
      _ ≤ C1 * (1 + Cm) ^ N1 * (1 + |Ca|) * H ^ (N1 + N2 + Na) +
          ‖Cp‖ * C2 * (1 + Cm) ^ N2 * (1 + |Ca|) * H ^ (N1 + N2 + Na) := by gcongr
      _ = _ := by ring
  calc Kb * I ≤ A * H ^ (N1 + N2 + Na) * I := mul_le_mul_of_nonneg_right hKbA hI0
    _ = A * I * H ^ (N1 + N2 + Na) := by ring
