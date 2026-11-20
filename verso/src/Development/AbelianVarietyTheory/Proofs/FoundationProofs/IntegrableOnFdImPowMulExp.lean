import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Establish `h` using `ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz`. Use `z.im_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem fd_half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

/- English proof (translation)
Rewrite using `[UpperHalfPlane.volume_eq_lintegral]`. Use `set S : Set ℂ := Complex.re ⁻¹' Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∩ Complex.im ⁻¹' Set.Ici (1 / 2 : ℝ) with hS`. Establish `hsub : ((↑) '' ModularGroup.fd : Set ℂ) ⊆ S`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `⟨abs_le.1 hz.2, fd_half_le_im hz⟩`.

Establish `hSm : MeasurableSet S` using `(Complex.measurable_re measurableSet_Icc).inter (Complex.measurable_im measurableSet_Ici)`. Use `lt_of_le_of_lt (lintegral_mono_set hsub) ?_` and prove the remaining obligations. Rewrite using `[← lintegral_indicator hSm]`. Use `set g : ℂ → ENNReal := fun z => ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) with hg`. Establish `e` using `(Complex.volume_preserving_equiv_real_prod.symm _).lintegral_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding (S.indicator g)`.

Rewrite using `[← e]`. Establish `hle : ∀ p : ℝ × ℝ, S.indicator g (Complex.measurableEquivRealProd.symm p) ≤ (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ENNReal)) p.1 * (Set.Ici (1 / 2 : ℝ)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) p.2`. Introduce and unpack `⟨x, y⟩`. Establish `hsy : Complex.measurableEquivRealProd.symm (x, y) = ⟨x, y⟩` using `rfl`. Rewrite using `[hsy]`.

Distinguish the cases in `hm : (⟨x, y⟩ : ℂ) ∈ S`. Take `⟨hx, hy⟩` from `id hm`. Establish `hx' : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)` using `hx`. Establish `hy' : y ∈ Set.Ici (1 / 2 : ℝ)` using `hy`. Rewrite using `[Set.indicator_of_mem hm, Set.indicator_of_mem hx', Set.indicator_of_mem hy', one_mul]`.

Apply `le_of_eq` to reduce the goal to its premises. Simplify using `only [hg]`. Rewrite using `[ENNReal.ofReal]`. Use `congr 1`. Use `ext`.

Simplify using `[sq_abs]`. Check the signs of the components of the expression. Rewrite using `[Set.indicator_of_notMem hm]`. Conclude with `bot_le`. Use `lt_of_le_of_lt (lintegral_mono hle) ?_` and prove the remaining obligations.

Rewrite using `[Measure.volume_eq_prod, lintegral_prod_mul (aemeasurable_const.indicator measurableSet_Icc) ((by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal (1 / y ^ 2)).aemeasurable.indicator measurableSet_Ici)]`. Rewrite using `[lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ici, setLIntegral_const, one_mul, Real.volume_Icc]`. Use `ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_` and prove the remaining obligations. Establish `h : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Set.Ioi (1 / 2 : ℝ))` using `integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)`. Establish `h' : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Set.Ici (1 / 2 : ℝ))`.

Rewrite using `[integrableOn_Ici_iff_integrableOn_Ioi]`. Use `h.congr_fun (fun y hy => ?_) measurableSet_Ioi` and prove the remaining obligations. Establish `hy0 : (0 : ℝ) ≤ y` using `le_trans (by norm_num) (le_of_lt hy)`. Simplify using `only`. Rewrite using `[Real.rpow_neg hy0, Real.rpow_two, one_div]`.

Conclude with `h'.lintegral_lt_top`.
-/
theorem fd_volume_lt_top : volume ModularGroup.fd < ⊤ := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  set S : Set ℂ := Complex.re ⁻¹' Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∩ Complex.im ⁻¹' Set.Ici (1 / 2 : ℝ)
    with hS
  have hsub : ((↑) '' ModularGroup.fd : Set ℂ) ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨abs_le.1 hz.2, fd_half_le_im hz⟩
  have hSm : MeasurableSet S :=
    (Complex.measurable_re measurableSet_Icc).inter (Complex.measurable_im measurableSet_Ici)
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  rw [← lintegral_indicator hSm]
  set g : ℂ → ENNReal := fun z => ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) with hg
  have e := (Complex.volume_preserving_equiv_real_prod.symm _).lintegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding (S.indicator g)
  rw [← e]
  have hle : ∀ p : ℝ × ℝ, S.indicator g (Complex.measurableEquivRealProd.symm p) ≤
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ENNReal)) p.1 *
      (Set.Ici (1 / 2 : ℝ)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) p.2 := by
    rintro ⟨x, y⟩
    have hsy : Complex.measurableEquivRealProd.symm (x, y) = ⟨x, y⟩ := rfl
    rw [hsy]
    by_cases hm : (⟨x, y⟩ : ℂ) ∈ S
    · obtain ⟨hx, hy⟩ := id hm
      have hx' : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := hx
      have hy' : y ∈ Set.Ici (1 / 2 : ℝ) := hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hx', Set.indicator_of_mem hy', one_mul]
      apply le_of_eq
      simp only [hg]
      rw [ENNReal.ofReal]
      congr 1
      ext
      simp [sq_abs]
      positivity
    · rw [Set.indicator_of_notMem hm]
      exact bot_le
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [Measure.volume_eq_prod, lintegral_prod_mul (aemeasurable_const.indicator measurableSet_Icc)
    ((by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal (1 / y ^ 2)).aemeasurable.indicator
      measurableSet_Ici)]
  rw [lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ici,
    setLIntegral_const, one_mul, Real.volume_Icc]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have h : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Set.Ioi (1 / 2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h' : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Set.Ici (1 / 2 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num) (le_of_lt hy)
    simp only
    rw [Real.rpow_neg hy0, Real.rpow_two, one_div]
  exact h'.lintegral_lt_top

/- English proof (translation)
Apply `IsClosed.measurableSet` to reduce the goal to its premises. Establish `h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)}` using `isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)`. Establish `h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2}` using `isClosed_le (UpperHalfPlane.continuous_re.abs) continuous_const`. Conclude with `h1.inter h2`.
-/
theorem fd_measurableSet : MeasurableSet ModularGroup.fd := by
  apply IsClosed.measurableSet
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (UpperHalfPlane.continuous_re.abs) continuous_const
  exact h1.inter h2

/- English proof (translation)
Establish `h` using `Real.pow_div_factorial_le_exp (δ * y) (mul_nonneg hδ.le hy) A`. Establish `hf : (0 : ℝ) < A.factorial` using `by exact_mod_cast A.factorial_pos`. Establish `hδA : 0 < δ ^ A` using `pow_pos hδ A`. Rewrite `h` using `[div_le_iff₀ hf, mul_pow]`. Rewrite using `[le_div_iff₀ hδA, neg_mul, Real.exp_neg]`.

Establish `he` using `Real.exp_pos (δ * y)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_mul_exp_neg_le (δ : ℝ) (A : ℕ) (hδ : 0 < δ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ A * Real.exp (-δ * y) ≤ (A.factorial : ℝ) / δ ^ A := by
  have h := Real.pow_div_factorial_le_exp (δ * y) (mul_nonneg hδ.le hy) A
  have hf : (0 : ℝ) < A.factorial := by exact_mod_cast A.factorial_pos
  have hδA : 0 < δ ^ A := pow_pos hδ A
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ hδA, neg_mul, Real.exp_neg]
  have he := Real.exp_pos (δ * y)
  calc y ^ A * (Real.exp (δ * y))⁻¹ * δ ^ A = δ ^ A * y ^ A * (Real.exp (δ * y))⁻¹ := by ring
    _ ≤ Real.exp (δ * y) * A.factorial * (Real.exp (δ * y))⁻¹ := by gcongr
    _ = A.factorial := by field_simp

/- English proof (translation)
Introduce `δ A hδ`. Use `Measure.integrableOn_of_bounded (M := (A.factorial : ℝ) / δ ^ A) fd_volume_lt_top.ne (by fun_prop : Continuous fun τ : ℍ => τ.im ^ A * Real.exp (-δ * τ.im)).aestronglyMeasurable ((ae_restrict_iff' fd_measurableSet).2 (Filter.Eventually.of_forall fun τ _ => ?_))` and prove the remaining obligations. Establish `hy` using `τ.im_pos.le`. Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Conclude with `pow_mul_exp_neg_le δ A hδ hy`.
-/
theorem integrableOn_fd_im_pow_mul_exp :
    ∀ (δ : ℝ) (A : ℕ), 0 < δ →
      IntegrableOn (fun τ : ℍ => τ.im ^ A * Real.exp (-δ * τ.im)) ModularGroup.fd := by
  intro δ A hδ
  refine Measure.integrableOn_of_bounded (M := (A.factorial : ℝ) / δ ^ A) fd_volume_lt_top.ne
    (by fun_prop : Continuous fun τ : ℍ => τ.im ^ A * Real.exp (-δ * τ.im)).aestronglyMeasurable
    ((ae_restrict_iff' fd_measurableSet).2 (Filter.Eventually.of_forall fun τ _ => ?_))
  have hy := τ.im_pos.le
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_mul_exp_neg_le δ A hδ hy

end GlobalTheory.EisM
