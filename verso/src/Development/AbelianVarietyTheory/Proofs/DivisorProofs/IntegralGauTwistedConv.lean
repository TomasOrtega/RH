import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}

/- English proof (translation)
Use `set m : V := (1 / 2 : ℝ) • (y - a) with hm`. Establish `hym : y - a = m + m`. Rewrite using `[hm, ← add_smul]`. Evaluate the numerical expressions. Establish `hself : ∀ x : V, ⟪x, J x⟫ = 0`.

Introduce `x`. Use `omJ_skew hJ x x` as an intermediate fact. Unfold `omJ at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsk : ∀ x z : V, ⟪z, J x⟫ = -⟪x, J z⟫` using `fun x z => by`.

Use `omJ_skew hJ x z` as an intermediate fact. Unfold `omJ at this`. Conclude with `this`. Establish `hpt : ∀ v : V, gau (v + m) * (gau (y - (v + m + a)) * cexp (π * I * ((omJ J (v + m) a + omJ J (v + m + a) y : ℝ) : ℂ))) = cexp (-(π : ℂ) * ‖v‖ ^ 2 + (π * I) * ⟪J (a + y), v⟫) * cexp (-(π : ℂ) * ‖m‖ ^ 2)`. Introduce `v`.

Establish `e1 : y - (v + m + a) = m - v`. Establish `hy : y = m + m + a` using `by rw [← hym]; abel`. Rewrite using `[hy]`. Normalize the expressions using the abelian group laws. Establish `h1 : ‖v + m‖ ^ 2 + ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2`.

Rewrite using `[e1, norm_add_sq_real, norm_sub_sq_real, real_inner_comm m v]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : omJ J (v + m) a + omJ J (v + m + a) y = ⟪J (a + y), v⟫`. Unfold `omJ`. Rewrite using `[real_inner_comm v (J (a + y)), hm]`.

Simplify using `only [map_add, inner_add_left, inner_add_right, real_inner_smul_left, inner_sub_left]`. Establish `h3` using `hsk a y`. Establish `h4` using `hself a`. Establish `h5` using `hself y`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1c : ((‖y - (v + m + a)‖ : ℝ) : ℂ) ^ 2 = 2 * (‖v‖ : ℂ) ^ 2 + 2 * (‖m‖ : ℂ) ^ 2 - (‖v + m‖ : ℂ) ^ 2`. Establish `h6 : ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 - ‖v + m‖ ^ 2` using `by linarith`. Conclude with `h6` after adjusting the coercions. Simplify using `only [gau, ← Complex.exp_add]`. Use `congr 1`.

Rewrite using `[h1c, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hshift` using `integral_add_right_eq_self (μ := (volume : Measure V)) (fun u => gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ)))) m`. Rewrite using `[← hshift]`. Simplify using `only [hpt]`.

Establish `hb : 0 < (π : ℂ).re` using `by simpa using Real.pi_pos`. Establish `hπ : (π : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Rewrite using `[integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb, div_self hπ, Complex.one_cpow, one_mul, LinearIsometryEquiv.norm_map, gau, gau, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Establish `h3 : ‖m‖ ^ 2 = ‖a‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2 - ‖a + y‖ ^ 2 / 4`.

Rewrite using `[hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow, norm_sub_sq_real, norm_add_sq_real, real_inner_comm y a]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3c : (‖m‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 / 2 + (‖y‖ : ℂ) ^ 2 / 2 - (‖a + y‖ : ℂ) ^ 2 / 4`. Conclude with `h3` after adjusting the coercions. Rewrite using `[h3c, mul_pow, I_sq]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_gau_twisted_conv (hJ : ∀ x, J (J x) = -x) (a y : V) :
    ∫ u, gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ))) = gau a * gau y := by
  set m : V := (1 / 2 : ℝ) • (y - a) with hm
  have hym : y - a = m + m := by
    rw [hm, ← add_smul]; norm_num
  have hself : ∀ x : V, ⟪x, J x⟫ = 0 := by
    intro x
    have := omJ_skew hJ x x
    unfold omJ at this
    linarith
  have hsk : ∀ x z : V, ⟪z, J x⟫ = -⟪x, J z⟫ := fun x z => by
    have := omJ_skew hJ x z
    unfold omJ at this
    exact this
  have hpt : ∀ v : V, gau (v + m) * (gau (y - (v + m + a)) *
      cexp (π * I * ((omJ J (v + m) a + omJ J (v + m + a) y : ℝ) : ℂ))) =
      cexp (-(π : ℂ) * ‖v‖ ^ 2 + (π * I) * ⟪J (a + y), v⟫) * cexp (-(π : ℂ) * ‖m‖ ^ 2) := by
    intro v
    have e1 : y - (v + m + a) = m - v := by
      have hy : y = m + m + a := by rw [← hym]; abel
      rw [hy]; abel
    have h1 : ‖v + m‖ ^ 2 + ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
      rw [e1, norm_add_sq_real, norm_sub_sq_real, real_inner_comm m v]; ring
    have h2 : omJ J (v + m) a + omJ J (v + m + a) y = ⟪J (a + y), v⟫ := by
      unfold omJ
      rw [real_inner_comm v (J (a + y)), hm]
      simp only [map_add, inner_add_left, inner_add_right, real_inner_smul_left, inner_sub_left]
      have h3 := hsk a y
      have h4 := hself a
      have h5 := hself y
      linarith
    have h1c : ((‖y - (v + m + a)‖ : ℝ) : ℂ) ^ 2 =
        2 * (‖v‖ : ℂ) ^ 2 + 2 * (‖m‖ : ℂ) ^ 2 - (‖v + m‖ : ℂ) ^ 2 := by
      have h6 : ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 - ‖v + m‖ ^ 2 := by linarith
      exact_mod_cast h6
    simp only [gau, ← Complex.exp_add]
    congr 1
    rw [h1c, h2]
    ring
  have hshift := integral_add_right_eq_self (μ := (volume : Measure V))
    (fun u => gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ)))) m
  rw [← hshift]
  simp only [hpt]
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb, div_self hπ, Complex.one_cpow, one_mul,
    LinearIsometryEquiv.norm_map, gau, gau, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h3 : ‖m‖ ^ 2 = ‖a‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2 - ‖a + y‖ ^ 2 / 4 := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow,
      norm_sub_sq_real, norm_add_sq_real, real_inner_comm y a]
    ring
  have h3c : (‖m‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 / 2 + (‖y‖ : ℂ) ^ 2 / 2 - (‖a + y‖ : ℂ) ^ 2 / 4 := by
    exact_mod_cast h3
  rw [h3c, mul_pow, I_sq]
  field_simp
  ring

/- English proof (translation)
Establish `hself : ∀ x : V, omJ J x x = 0` using `fun x => by`. Use `omJ_skew hJ x x` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set F : V → V → B := fun u z => (gau u * (gau (z - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) z : ℝ) : ℂ)))) • ρ z f with hF`. Establish `hin : ∀ u, gau u • ρ u (ρ a (proj h f)) = ∫ z, F u z`.

Introduce `u`. Rewrite using `[h.2.1 u a, proj_apply h f, ← (ρ (u + a)).integral_comp_comm (h.integrable f), ← integral_smul, ← integral_smul, ← integral_add_right_eq_self (F u) (u + a)]`. Use `congr 1`. Use extensionality with `w`. Establish `hw : omJ J (u + a) (w + (u + a)) = omJ J (u + a) w`.

Establish `h0` using `hself (u + a)`. Unfold `omJ at h0 ⊢`. Rewrite using `[map_add, inner_add_right, h0, add_zero]`. Use `show _ = (gau u * (gau (w + (u + a) - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) (w + (u + a)) : ℝ) : ℂ)))) • ρ (w + (u + a)) f`. Rewrite using `[add_sub_cancel_right, hw, add_comm w (u + a), map_smul, h.2.1 (u + a) w, smul_smul, smul_smul, smul_smul]`.

Use `congr 1`. Use `push_cast`. Rewrite using `[mul_add, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `he : ∀ r : ℝ, ‖cexp (π * I * (r : ℂ))‖ = 1` using `fun r => by`.

Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules. Establish `hnorm : ∀ u z, ‖F u z‖ = ‖gau u‖ * (‖gau (z - (u + a))‖ * ‖f‖)`. Introduce `u z`. Simplify using `only [hF, norm_smul, norm_mul, h.2.2.1]`.

Rewrite using `[he, mul_one, mul_assoc]`. Establish `hom : Continuous fun p : V × V => omJ J p.1 p.2`. Unfold `omJ`. Conclude with `continuous_fst.inner (J.continuous.comp continuous_snd)`. Establish `hcont : Continuous (Function.uncurry F)` using `by show Continuous fun p : V × V => (gau p.1 * (gau (p.2 - (p.1 + a)) * cexp (π * I * ((omJ J p.1 a + omJ J (p.1 + a) p.2 : ℝ) : ℂ)))) • ρ p.2 f`.

Use `Continuous.smul ?_ ((h.2.2.2 f).comp continuous_snd)` and prove the remaining obligations. Use `(continuous_gau.comp continuous_fst).mul ((continuous_gau.comp (continuous_snd.sub (continuous_fst.add continuous_const))).mul ?_)` and prove the remaining obligations. Use `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))` and prove the remaining obligations. Conclude with `(hom.comp (continuous_fst.prodMk continuous_const)).add (hom.comp ((continuous_fst.add continuous_const).prodMk continuous_snd))`. Establish `hint : Integrable (Function.uncurry F) ((volume : Measure V).prod volume)`.

Rewrite using `[integrable_prod_iff hcont.aestronglyMeasurable]`. Prove the components needed by the constructor for the conclusion. Use `Filter.Eventually.of_forall fun u => ?_` and prove the remaining obligations. Establish `hm : AEStronglyMeasurable (fun z => Function.uncurry F (u, z)) volume` using `(hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable`. Rewrite using `[← integrable_norm_iff hm]`.

Simplify using `only [Function.uncurry_apply_pair, hnorm]`. Conclude with `(((integrable_gau (V := V)).norm.comp_sub_right (u + a)).mul_const ‖f‖).const_mul ‖gau u‖`. Simplify using `only [Function.uncurry_apply_pair, hnorm]`. Simplify using `only [integral_const_mul, integral_mul_const, integral_sub_right_eq_self (‖gau ·‖)]`. Conclude with `(integrable_gau (V := V)).norm.mul_const _`.

Rewrite using `[proj_apply h (ρ a (proj h f))]`. Repeatedly rewrite using `[hin]`. Rewrite using `[integral_integral_swap hint]`. Establish `hinner : ∀ z, ∫ u, F u z = (gau a * gau z) • ρ z f`. Introduce `z`.

Simplify using `only [hF]`. Rewrite using `[integral_smul_const, integral_gau_twisted_conv hJ a z]`. Repeatedly rewrite using `[hinner]`. Rewrite using `[proj_apply h f, ← integral_smul]`. Use `congr 1`.

Use extensionality with `z`. Rewrite using `[smul_smul]`.
-/
theorem proj_heis_proj {ρ : V → B →L[ℂ] B} (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a : V) (f : B) :
    proj h (ρ a (proj h f)) = gau a • proj h f := by
  have hself : ∀ x : V, omJ J x x = 0 := fun x => by
    have := omJ_skew hJ x x
    linarith
  set F : V → V → B := fun u z =>
    (gau u * (gau (z - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) z : ℝ) : ℂ)))) • ρ z f with hF
  have hin : ∀ u, gau u • ρ u (ρ a (proj h f)) = ∫ z, F u z := by
    intro u
    rw [h.2.1 u a, proj_apply h f, ← (ρ (u + a)).integral_comp_comm (h.integrable f), ← integral_smul,
      ← integral_smul, ← integral_add_right_eq_self (F u) (u + a)]
    congr 1
    ext w
    have hw : omJ J (u + a) (w + (u + a)) = omJ J (u + a) w := by
      have h0 := hself (u + a)
      unfold omJ at h0 ⊢
      rw [map_add, inner_add_right, h0, add_zero]
    show _ = (gau u * (gau (w + (u + a) - (u + a)) *
      cexp (π * I * ((omJ J u a + omJ J (u + a) (w + (u + a)) : ℝ) : ℂ)))) • ρ (w + (u + a)) f
    rw [add_sub_cancel_right, hw, add_comm w (u + a), map_smul, h.2.1 (u + a) w, smul_smul, smul_smul,
      smul_smul]
    congr 1
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have he : ∀ r : ℝ, ‖cexp (π * I * (r : ℂ))‖ = 1 := fun r => by
    rw [Complex.norm_exp]
    simp
  have hnorm : ∀ u z, ‖F u z‖ = ‖gau u‖ * (‖gau (z - (u + a))‖ * ‖f‖) := by
    intro u z
    simp only [hF, norm_smul, norm_mul, h.2.2.1]
    rw [he, mul_one, mul_assoc]
  have hom : Continuous fun p : V × V => omJ J p.1 p.2 := by
    unfold omJ
    exact continuous_fst.inner (J.continuous.comp continuous_snd)
  have hcont : Continuous (Function.uncurry F) := by
    show Continuous fun p : V × V => (gau p.1 * (gau (p.2 - (p.1 + a)) *
      cexp (π * I * ((omJ J p.1 a + omJ J (p.1 + a) p.2 : ℝ) : ℂ)))) • ρ p.2 f
    refine Continuous.smul ?_ ((h.2.2.2 f).comp continuous_snd)
    refine (continuous_gau.comp continuous_fst).mul
      ((continuous_gau.comp (continuous_snd.sub (continuous_fst.add continuous_const))).mul ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact (hom.comp (continuous_fst.prodMk continuous_const)).add
      (hom.comp ((continuous_fst.add continuous_const).prodMk continuous_snd))
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod volume) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun u => ?_
      have hm : AEStronglyMeasurable (fun z => Function.uncurry F (u, z)) volume :=
        (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      rw [← integrable_norm_iff hm]
      simp only [Function.uncurry_apply_pair, hnorm]
      exact (((integrable_gau (V := V)).norm.comp_sub_right (u + a)).mul_const ‖f‖).const_mul ‖gau u‖
    · simp only [Function.uncurry_apply_pair, hnorm]
      simp only [integral_const_mul, integral_mul_const, integral_sub_right_eq_self (‖gau ·‖)]
      exact (integrable_gau (V := V)).norm.mul_const _
  rw [proj_apply h (ρ a (proj h f))]
  simp_rw [hin]
  rw [integral_integral_swap hint]
  have hinner : ∀ z, ∫ u, F u z = (gau a * gau z) • ρ z f := by
    intro z
    simp only [hF]
    rw [integral_smul_const, integral_gau_twisted_conv hJ a z]
  simp_rw [hinner]
  rw [proj_apply h f, ← integral_smul]
  congr 1
  ext z
  rw [smul_smul]

end GlobalTheory.RealWeil
