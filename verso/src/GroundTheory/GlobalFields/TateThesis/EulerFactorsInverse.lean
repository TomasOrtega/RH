import Mathlib
import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite

open NumberField InfinitePlace InfinitePlace.Completion Complex
open scoped Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Assume the negation of the conclusion as `hab`. Establish `hne : a - b ≠ 0` using `sub_ne_zero.2 hab`. Use `set t : ℝ := π / (a - b)`. Establish `ht : (a - b) * t = π` using `by simp only [t]; field_simp`. Establish `h1 : Complex.exp ((((a - b) * t : ℝ) : ℂ) * I) = 1`.

Establish `e : ((((a - b) * t : ℝ) : ℂ) * I) = (a : ℂ) * t * I - (b : ℂ) * t * I` using `by push_cast; ring`. Rewrite using `[e, Complex.exp_sub, h t, div_self (Complex.exp_ne_zero _)]`. Rewrite `h1` using `[ht, Complex.exp_eq_one_iff]`. Take `⟨n, hn⟩` from `h1`. Establish `h2 : (π : ℂ) = ((n * (2 * π) : ℝ) : ℂ)`.

Use `mul_right_cancel₀ I_ne_zero (hn.trans ?_)` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : π = n * (2 * π)` using `by exact_mod_cast h2`. Establish `h4 : (1 : ℝ) = 2 * n`.

Establish `hπ : π ≠ 0` using `Real.pi_ne_zero`. Clear denominators, using `at h3` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : (1 : ℤ) = 2 * n` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_of_forall_exp_mul_I {a b : ℝ}
    (h : ∀ t : ℝ, Complex.exp (a * t * I) = Complex.exp (b * t * I)) : a = b := by
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.2 hab
  set t : ℝ := π / (a - b)
  have ht : (a - b) * t = π := by simp only [t]; field_simp
  have h1 : Complex.exp ((((a - b) * t : ℝ) : ℂ) * I) = 1 := by
    have e : ((((a - b) * t : ℝ) : ℂ) * I) = (a : ℂ) * t * I - (b : ℂ) * t * I := by
      push_cast; ring
    rw [e, Complex.exp_sub, h t, div_self (Complex.exp_ne_zero _)]
  rw [ht, Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have h2 : (π : ℂ) = ((n * (2 * π) : ℝ) : ℂ) := by
    refine mul_right_cancel₀ I_ne_zero (hn.trans ?_)
    push_cast; ring
  have h3 : π = n * (2 * π) := by exact_mod_cast h2
  have h4 : (1 : ℝ) = 2 * n := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp at h3
    linarith
  have h5 : (1 : ℤ) = 2 * n := by exact_mod_cast h4
  omega

omit [NumberField K] in

/- English proof (translation)
Distinguish the cases in `hw : w.IsReal`. Take `⟨a, ha⟩` from `surjective_extensionEmbeddingOfIsReal hw r`. Conclude with `⟨a, by rw [← extensionEmbeddingOfIsReal_apply hw, ha]⟩`. Conclude with `surjective_extensionEmbedding_of_isComplex (not_isReal_iff_isComplex.1 hw) (r : ℂ)`.
-/
theorem exists_extensionEmbedding_eq_ofReal (w : InfinitePlace K) (r : ℝ) :
    ∃ a : w.Completion, extensionEmbedding w a = r := by
  by_cases hw : w.IsReal
  · obtain ⟨a, ha⟩ := surjective_extensionEmbeddingOfIsReal hw r
    exact ⟨a, by rw [← extensionEmbeddingOfIsReal_apply hw, ha]⟩
  · exact surjective_extensionEmbedding_of_isComplex (not_isReal_iff_isComplex.1 hw) (r : ℂ)

omit [NumberField K] in
/- English proof (translation)
The claim follows from `(isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a`.
-/
theorem norm_extensionEmbedding' (w : InfinitePlace K) (a : w.Completion) :
    ‖extensionEmbedding w a‖ = ‖a‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a

/- English proof (translation)
Rewrite using `[cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← ofReal_log (Real.exp_pos t).le, Real.log_exp]`.
-/
theorem ofReal_exp_cpow (t : ℝ) (c : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ c = Complex.exp (t * c) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← ofReal_log
    (Real.exp_pos t).le, Real.log_exp]

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

/- English proof (translation)
Use `set q := χ.infiniteParams w`. Establish `hq1 : w.IsReal → 0 ≤ q.1 ∧ q.1 < 2` using `(χ.exists_infiniteParams w).choose_spec.1`. Establish `hq2` using `(χ.exists_infiniteParams w).choose_spec.2`. Establish `heq : ∀ a : (w.Completion)ˣ, (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 * ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) = (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ q.1 * ((‖(a : w.Completion)‖ ^ w.mult …` using `fun a ↦ (hp2 a).symm.trans (hq2 a)`. Establish `hM : (1 : ℝ) ≤ w.mult` using `by exact_mod_cast InfinitePlace.one_le_mult`.

Establish `hτ : p.2 = q.2`. Establish `key : ∀ t : ℝ, Complex.exp ((w.mult * p.2 : ℝ) * t * I) = Complex.exp ((w.mult * q.2 : ℝ) * t * I)`. Introduce `t`. Take `⟨a, ha⟩` from `exists_extensionEmbedding_eq_ofReal w (Real.exp t)`. Establish `ha0 : a ≠ 0` using `fun h0 ↦ by`.

Rewrite `ha` using `[h0, map_zero]`. Conclude with `(Real.exp_pos t).ne' (by exact_mod_cast ha.symm)`. Establish `hn : ‖a‖ = Real.exp t`. Rewrite using `[← norm_extensionEmbedding', ha, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]`. Establish `h` using `heq (Units.mk0 a ha0)`.

Simplify using `only [Units.val_mk0, ha, hn, div_self (by exact_mod_cast (Real.exp_pos t).ne' : ((Real.exp t : ℝ) : ℂ) ≠ 0), one_zpow, one_mul, ← Real.exp_nat_mul, ofReal_exp_cpow] at h`. Apply the tactic sequence `convert h using 2 <;> push_cast <;> ring`. Use `eq_of_forall_exp_mul_I key` as an intermediate fact. Establish `hM0 : (w.mult : ℝ) ≠ 0` using `by positivity`. Conclude with `mul_left_cancel₀ hM0 this`.

Establish `hm : ∀ a : (w.Completion)ˣ, (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 = (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ q.1`. Introduce `a`. Establish `h` using `heq a`. Rewrite `h` using `[hτ]`. Establish `hpos : (0 : ℝ) < ‖(a : w.Completion)‖ ^ w.mult` using `pow_pos (norm_pos_iff.2 a.ne_zero) _`.

Establish `hne : ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((q.2 : ℂ) * I) ≠ 0`. Rewrite using `[cpow_def_of_ne_zero (by exact_mod_cast hpos.ne')]`. Conclude with `Complex.exp_ne_zero _`. Conclude with `mul_right_cancel₀ hne h`. Use `Prod.ext ?_ hτ` and prove the remaining obligations.

Distinguish the cases in `hw : w.IsReal`. Take `⟨hp0, hp2'⟩` from `hp1 hw`. Take `⟨hq0, hq2'⟩` from `hq1 hw`. Take `⟨a, ha⟩` from `exists_extensionEmbedding_eq_ofReal w (-1)`. Establish `ha0 : a ≠ 0` using `fun h0 ↦ by rw [h0, map_zero] at ha; norm_num at ha`.

Establish `hn : ‖a‖ = 1` using `by rw [← norm_extensionEmbedding', ha]; simp`. Establish `h` using `hm (Units.mk0 a ha0)`. Simplify using `only [Units.val_mk0, ha, hn, ofReal_one, div_one, ofReal_neg] at h`. Apply the tactic sequence `rcases (show p.1 = 0 ∨ p.1 = 1 by omega) with h1 | h1 <;>`. Apply the tactic sequence `rcases (show q.1 = 0 ∨ q.1 = 1 by omega) with h2 | h2 <;> rw [h1, h2] at h ⊢ <;>`.

Evaluate the numerical expressions using `at h`. Establish `hc` using `not_isReal_iff_isComplex.1 hw`. Establish `key : ∀ θ : ℝ, Complex.exp ((p.1 : ℝ) * θ * I) = Complex.exp ((q.1 : ℝ) * θ * I)`. Introduce `θ`. Take `⟨a, ha⟩` from `surjective_extensionEmbedding_of_isComplex hc (Complex.exp (θ * I))`.

Establish `ha0 : a ≠ 0` using `fun h0 ↦ by`. Rewrite `ha` using `[h0, map_zero]`. Conclude with `Complex.exp_ne_zero _ ha.symm`. Establish `hn : ‖a‖ = 1`. Rewrite using `[← norm_extensionEmbedding', ha, Complex.norm_exp_ofReal_mul_I]`.

Establish `h` using `hm (Units.mk0 a ha0)`. Simplify using `only [Units.val_mk0, ha, hn, ofReal_one, div_one, ← Complex.exp_int_mul] at h`. Apply the tactic sequence `convert h using 2 <;> push_cast <;> ring`. Conclude with `eq_of_forall_exp_mul_I key` after adjusting the coercions.
-/
theorem infiniteParams_unique (w : InfinitePlace K) {p : ℤ × ℝ}
    (hp1 : w.IsReal → 0 ≤ p.1 ∧ p.1 < 2)
    (hp2 : ∀ a : (w.Completion)ˣ, (χ.infiniteComponent w a : ℂ) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I)) :
    p = χ.infiniteParams w := by
  set q := χ.infiniteParams w
  have hq1 : w.IsReal → 0 ≤ q.1 ∧ q.1 < 2 := (χ.exists_infiniteParams w).choose_spec.1
  have hq2 := (χ.exists_infiniteParams w).choose_spec.2
  have heq : ∀ a : (w.Completion)ˣ,
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ q.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((q.2 : ℂ) * I) :=
    fun a ↦ (hp2 a).symm.trans (hq2 a)
  have hM : (1 : ℝ) ≤ w.mult := by exact_mod_cast InfinitePlace.one_le_mult

  have hτ : p.2 = q.2 := by
    have key : ∀ t : ℝ, Complex.exp ((w.mult * p.2 : ℝ) * t * I) =
        Complex.exp ((w.mult * q.2 : ℝ) * t * I) := by
      intro t
      obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal w (Real.exp t)
      have ha0 : a ≠ 0 := fun h0 ↦ by
        rw [h0, map_zero] at ha
        exact (Real.exp_pos t).ne' (by exact_mod_cast ha.symm)
      have hn : ‖a‖ = Real.exp t := by
        rw [← norm_extensionEmbedding', ha, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos t)]
      have h := heq (Units.mk0 a ha0)
      simp only [Units.val_mk0, ha, hn, div_self (by exact_mod_cast (Real.exp_pos t).ne' :
        ((Real.exp t : ℝ) : ℂ) ≠ 0), one_zpow, one_mul, ← Real.exp_nat_mul,
        ofReal_exp_cpow] at h
      convert h using 2 <;> push_cast <;> ring
    have := eq_of_forall_exp_mul_I key
    have hM0 : (w.mult : ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hM0 this

  have hm : ∀ a : (w.Completion)ˣ,
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ q.1 := by
    intro a
    have h := heq a
    rw [hτ] at h
    have hpos : (0 : ℝ) < ‖(a : w.Completion)‖ ^ w.mult := pow_pos (norm_pos_iff.2 a.ne_zero) _
    have hne : ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((q.2 : ℂ) * I) ≠ 0 := by
      rw [cpow_def_of_ne_zero (by exact_mod_cast hpos.ne')]
      exact Complex.exp_ne_zero _
    exact mul_right_cancel₀ hne h
  refine Prod.ext ?_ hτ
  by_cases hw : w.IsReal
  · obtain ⟨hp0, hp2'⟩ := hp1 hw
    obtain ⟨hq0, hq2'⟩ := hq1 hw
    obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal w (-1)
    have ha0 : a ≠ 0 := fun h0 ↦ by rw [h0, map_zero] at ha; norm_num at ha
    have hn : ‖a‖ = 1 := by rw [← norm_extensionEmbedding', ha]; simp
    have h := hm (Units.mk0 a ha0)
    simp only [Units.val_mk0, ha, hn, ofReal_one, div_one, ofReal_neg] at h
    rcases (show p.1 = 0 ∨ p.1 = 1 by omega) with h1 | h1 <;>
      rcases (show q.1 = 0 ∨ q.1 = 1 by omega) with h2 | h2 <;> rw [h1, h2] at h ⊢ <;>
      norm_num at h
  · have hc := not_isReal_iff_isComplex.1 hw
    have key : ∀ θ : ℝ, Complex.exp ((p.1 : ℝ) * θ * I) = Complex.exp ((q.1 : ℝ) * θ * I) := by
      intro θ
      obtain ⟨a, ha⟩ := surjective_extensionEmbedding_of_isComplex hc (Complex.exp (θ * I))
      have ha0 : a ≠ 0 := fun h0 ↦ by
        rw [h0, map_zero] at ha
        exact Complex.exp_ne_zero _ ha.symm
      have hn : ‖a‖ = 1 := by
        rw [← norm_extensionEmbedding', ha, Complex.norm_exp_ofReal_mul_I]
      have h := hm (Units.mk0 a ha0)
      simp only [Units.val_mk0, ha, hn, ofReal_one, div_one, ← Complex.exp_int_mul] at h
      convert h using 2 <;> push_cast <;> ring
    exact_mod_cast eq_of_forall_exp_mul_I key

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inv_toIdele (x : IdeleGroup K) : (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localComponent_inv (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : (χ⁻¹).localComponent v a = (χ.localComponent v a)⁻¹ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infiniteComponent_inv (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    (χ⁻¹).infiniteComponent w a = (χ.infiniteComponent w a)⁻¹ := rfl

/- English proof (translation)
Establish `hker : (χ⁻¹).toIdele.ker = χ.toIdele.ker`. Use extensionality with `x`. Simplify using `only [MonoidHom.mem_ker, inv_toIdele, inv_eq_one]`. Establish `h1 : χ⁻¹.conductor ∣ χ.conductor`. Rewrite using `[← (χ⁻¹).map_idealLevel_le_ker_iff χ.conductor_ne_bot, hker]`.

Conclude with `χ.map_idealLevel_conductor_le_ker`. Establish `h2 : χ.conductor ∣ χ⁻¹.conductor`. Rewrite using `[← χ.map_idealLevel_le_ker_iff (χ⁻¹).conductor_ne_bot, ← hker]`. Conclude with `(χ⁻¹).map_idealLevel_conductor_le_ker`. Conclude with `le_antisymm (Ideal.le_of_dvd h2) (Ideal.le_of_dvd h1)`.
-/
theorem conductor_inv : χ⁻¹.conductor = χ.conductor := by
  have hker : (χ⁻¹).toIdele.ker = χ.toIdele.ker := by
    ext x
    simp only [MonoidHom.mem_ker, inv_toIdele, inv_eq_one]
  have h1 : χ⁻¹.conductor ∣ χ.conductor := by
    rw [← (χ⁻¹).map_idealLevel_le_ker_iff χ.conductor_ne_bot, hker]
    exact χ.map_idealLevel_conductor_le_ker
  have h2 : χ.conductor ∣ χ⁻¹.conductor := by
    rw [← χ.map_idealLevel_le_ker_iff (χ⁻¹).conductor_ne_bot, ← hker]
    exact (χ⁻¹).map_idealLevel_conductor_le_ker
  exact le_antisymm (Ideal.le_of_dvd h2) (Ideal.le_of_dvd h1)

open Classical in

/- English proof (translation)
Use `symm`. Use `(χ⁻¹).infiniteParams_unique w ?_ fun a ↦ ?_` and prove the remaining obligations. Introduce `hw`. Rewrite using `[if_pos hw]`. Conclude with `χ.infiniteWeight_of_isReal hw`.

Rewrite using `[infiniteComponent_inv, Circle.coe_inv, χ.infiniteComponent_eq]`. Simplify using `only`. Rewrite using `[mul_inv, ofReal_neg, neg_mul, cpow_neg]`. Use `congr 1`. Use `split_ifs with hw`.

Establish `hι : extensionEmbedding w (a : w.Completion) = ((extensionEmbeddingOfIsReal hw (a : w.Completion) : ℝ) : ℂ)` using `(extensionEmbeddingOfIsReal_apply hw _).symm`. Establish `hn : ‖(a : w.Completion)‖ = |extensionEmbeddingOfIsReal hw (a : w.Completion)|`. Rewrite using `[← Real.norm_eq_abs]`. Conclude with `((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm`. Establish `hx0 : extensionEmbeddingOfIsReal hw (a : w.Completion) ≠ 0` using `(map_ne_zero_iff _ (extensionEmbeddingOfIsReal hw).injective).2 a.ne_zero`.

Rewrite using `[hι, hn, ofReal_div_abs_eq_sign hx0, ← zpow_neg, ← inv_zpow']`. Use `congr 1`. Break down `lt_or_gt_of_ne hx0 with h | h` into its components or cases. Rewrite using `[Real.sign_of_neg h]`. Use `push_cast`.

Evaluate the numerical expressions. Rewrite using `[Real.sign_of_pos h]`. Use `push_cast`. Evaluate the numerical expressions. Rewrite using `[zpow_neg]`.
-/
theorem infiniteParams_inv (w : InfinitePlace K) :
    (χ⁻¹).infiniteParams w =
      (if w.IsReal then χ.infiniteWeight w else -χ.infiniteWeight w, -χ.infiniteTau w) := by
  symm
  refine (χ⁻¹).infiniteParams_unique w ?_ fun a ↦ ?_
  · intro hw
    rw [if_pos hw]
    exact χ.infiniteWeight_of_isReal hw
  · rw [infiniteComponent_inv, Circle.coe_inv, χ.infiniteComponent_eq]
    simp only
    rw [mul_inv, ofReal_neg, neg_mul, cpow_neg]
    congr 1
    split_ifs with hw
    ·
      have hι : extensionEmbedding w (a : w.Completion) =
          ((extensionEmbeddingOfIsReal hw (a : w.Completion) : ℝ) : ℂ) :=
        (extensionEmbeddingOfIsReal_apply hw _).symm
      have hn : ‖(a : w.Completion)‖ = |extensionEmbeddingOfIsReal hw (a : w.Completion)| := by
        rw [← Real.norm_eq_abs]
        exact ((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm
      have hx0 : extensionEmbeddingOfIsReal hw (a : w.Completion) ≠ 0 :=
        (map_ne_zero_iff _ (extensionEmbeddingOfIsReal hw).injective).2 a.ne_zero
      rw [hι, hn, ofReal_div_abs_eq_sign hx0, ← zpow_neg, ← inv_zpow']
      congr 1
      rcases lt_or_gt_of_ne hx0 with h | h
      · rw [Real.sign_of_neg h]; push_cast; norm_num
      · rw [Real.sign_of_pos h]; push_cast; norm_num
    · rw [zpow_neg]

/- English proof (translation)
Rewrite using `[infiniteWeight, infiniteParams_inv, if_pos hw]`.
-/
theorem infiniteWeight_inv_of_isReal {w : InfinitePlace K} (hw : w.IsReal) :
    (χ⁻¹).infiniteWeight w = χ.infiniteWeight w := by
  rw [infiniteWeight, infiniteParams_inv, if_pos hw]

/- English proof (translation)
Rewrite using `[infiniteWeight, infiniteParams_inv, if_neg (not_isReal_iff_isComplex.2 hw)]`.
-/
theorem infiniteWeight_inv_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) :
    (χ⁻¹).infiniteWeight w = -χ.infiniteWeight w := by
  rw [infiniteWeight, infiniteParams_inv, if_neg (not_isReal_iff_isComplex.2 hw)]

end HeckeCharacter

end

end GroundTheory.Global
