import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

/- English proof (translation)
Take `⟨C, hC⟩` from `hH.bdd`. Establish `hmF : MeasurableSet (𝓕 ∩ band)` using `hS.meas.inter hmb`. Use `Measure.integrableOn_of_bounded (M := C * (2 : ℝ) ^ |s.re|) hS.vol.ne (measurable_w hH c s).aestronglyMeasurable ?_` and prove the remaining obligations. Use `(ae_restrict_iff' hmF).2 (Eventually.of_forall fun g hg => ?_)` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hg.2`.

Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1)`. Establish `hp : (Dt g) ^ s.re ≤ (2 : ℝ) ^ |s.re|` using `(Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self _)).trans (Real.rpow_le_rpow (Dt_pos g).le h2.le (abs_nonneg _))`. Rewrite using `[norm_mul, norm_mul, norm_cdet, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]`. Conclude with `mul_le_mul (hC g) hp (Real.rpow_nonneg (Dt_pos g).le _) hC0`.
-/
theorem integrableOn_band_w {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd}
    {H : G2 → ℂ} (c : HeckeCharacter ℚ) (hS : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (s : ℂ)
    (hmb : MeasurableSet band) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ band) μ := by
  obtain ⟨C, hC⟩ := hH.bdd
  have hmF : MeasurableSet (𝓕 ∩ band) := hS.meas.inter hmb
  refine Measure.integrableOn_of_bounded (M := C * (2 : ℝ) ^ |s.re|) hS.vol.ne
    (measurable_w hH c s).aestronglyMeasurable ?_
  refine (ae_restrict_iff' hmF).2 (Eventually.of_forall fun g hg => ?_)
  obtain ⟨h1, h2⟩ := hg.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hp : (Dt g) ^ s.re ≤ (2 : ℝ) ^ |s.re| :=
    (Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self _)).trans
      (Real.rpow_le_rpow (Dt_pos g).le h2.le (abs_nonneg _))
  rw [norm_mul, norm_mul, norm_cdet, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
  exact mul_le_mul (hC g) hp (Real.rpow_nonneg (Dt_pos g).le _) hC0

/- English proof (translation)
Establish `h2 : (2 : ℂ).arg ≠ Real.pi`. Rewrite using `[show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]`. Conclude with `Real.pi_pos.ne`. Rewrite using `[show (((1 / 2 : ℝ)) : ℂ) = (2 : ℂ)⁻¹ by push_cast; norm_num, Complex.inv_cpow _ _ h2, Complex.cpow_neg]`.
-/
theorem cpow_half (s : ℂ) : (((1 / 2 : ℝ)) : ℂ) ^ s = 2 ^ (-s) := by
  have h2 : (2 : ℂ).arg ≠ Real.pi := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_pos.ne
  rw [show (((1 / 2 : ℝ)) : ℂ) = (2 : ℂ)⁻¹ by push_cast; norm_num, Complex.inv_cpow _ _ h2,
    Complex.cpow_neg]

/- English proof (translation)
Introduce `μ 𝓕 mK 𝓓 H c hG hS hH hc s hI`. Use `set w : G2 → ℂ := fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s with hw`. Take `⟨-, hr, hT⟩` from `hG μ 𝓕 mK 𝓓 hS`. Take `⟨z, hz2, hzc⟩` from `hr (1 / 2) (by norm_num)`. Establish `hzc'` using `hzc c hc`.

Establish `hm1 : MeasurableSet {g : G2 | Dt g < 1}` using `measurableSet_lt measurable_Dt measurable_const`. Establish `hm2 : MeasurableSet {g : G2 | Dt g < 2}` using `measurableSet_lt measurable_Dt measurable_const`. Establish `hmb : MeasurableSet band` using `(measurableSet_le measurable_const measurable_Dt).inter hm2`. Establish `hwm : Measurable w` using `measurable_w hH c s`. Establish `hset : {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} = {g : G2 | Dt g < 1}` using `rfl`.

Establish `hFm : Measurable (Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w)` using `hwm.indicator hm1`. Establish `hFl : LInv (Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w)` using `linv_ind (linv_w hH c s) _`. Establish `hinv : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) ∂μ = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w g ∂μ` using `(hT (fun g : G2 => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hFm hFl`. Establish `hpt : ∀ g : G2, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) = 2 ^ (-s) * Set.indicator {g : G2 | Dt g < 2} w g`. Introduce `g`.

Establish `hD : Dt (dg2 z z * g) = 1 / 2 * Dt g` using `by rw [Dt_dg, hz2]`. Establish `hwg : w (dg2 z z * g) = 2 ^ (-s) * w g`. Simplify using `only [hw]`. Rewrite using `[hH.cen z g, cdet_dg c z hzc' g, cpow_dg, hz2, cpow_half]`. Expand and normalize the polynomial expressions, which then agree.

Distinguish the cases in `h : Dt g < 2`. Establish `h' : dg2 z z * g ∈ {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)}`. Simplify using `only [Set.mem_setOf_eq, Set.mem_Iio, hD]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Set.indicator_of_mem h', Set.indicator_of_mem (show g ∈ {g : G2 | Dt g < 2} from h), hwg]`.

Establish `h' : dg2 z z * g ∉ {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)}`. Simplify using `only [Set.mem_setOf_eq, Set.mem_Iio, hD]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Set.indicator_of_notMem h', Set.indicator_of_notMem (show g ∉ {g : G2 | Dt g < 2} from h), mul_zero]`. Establish `e1 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) ∂μ = 2 ^ (-s) * ∫ g in 𝓕 ∩ {g : G2 | Dt g < 2}, w g ∂μ`.

Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_const_mul, setIntegral_indicator hm2]`. Establish `e2 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w g ∂μ = GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s`. Rewrite using `[hset, setIntegral_indicator hm1]`. Both sides reduce to the same expression.

Establish `hun : 𝓕 ∩ {g : G2 | Dt g < 2} = (𝓕 ∩ {g : G2 | Dt g < 1}) ∪ (𝓕 ∩ band)`. Use extensionality with `g`. Simplify using `only [band, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Distinguish the cases in `h : Dt g < 1`. Conclude with `Or.inl ⟨h1, h⟩`. Conclude with `Or.inr ⟨h1, not_lt.1 h, h2⟩`. Introduce and unpack `(⟨h1, h2⟩ | ⟨h1, -, h2⟩)`. Conclude with `⟨h1, by linarith⟩`.

Conclude with `⟨h1, h2⟩`. Establish `hdis : Disjoint (𝓕 ∩ {g : G2 | Dt g < 1}) (𝓕 ∩ band)`. Use `Set.disjoint_left.2 fun g hg hb => ?_` and prove the remaining obligations. Establish `h1 : Dt g < 1` using `hg.2`. Establish `h2 : 1 ≤ Dt g` using `hb.2.1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3 : ∫ g in 𝓕 ∩ {g : G2 | Dt g < 2}, w g ∂μ = GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s + GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s`. Rewrite using `[hun, setIntegral_union hdis (hS.meas.inter hmb) hI (integrableOn_band_w c hS hH s hmb)]`. Both sides reduce to the same expression. Establish `key : 2 ^ (-s) * (GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s + GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s) = GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s`.

Rewrite using `[← e3, ← e1, hinv, e2]`. Take the linear combination `-key`.
-/
theorem Jl_shift : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ →
    GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s * (1 - 2 ^ (-s)) = GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s * 2 ^ (-s) := by
  intro μ 𝓕 mK 𝓓 H c hG hS hH hc s hI
  set w : G2 → ℂ := fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s with hw
  obtain ⟨-, hr, hT⟩ := hG μ 𝓕 mK 𝓓 hS
  obtain ⟨z, hz2, hzc⟩ := hr (1 / 2) (by norm_num)
  have hzc' := hzc c hc
  have hm1 : MeasurableSet {g : G2 | Dt g < 1} := measurableSet_lt measurable_Dt measurable_const
  have hm2 : MeasurableSet {g : G2 | Dt g < 2} := measurableSet_lt measurable_Dt measurable_const
  have hmb : MeasurableSet band :=
    (measurableSet_le measurable_const measurable_Dt).inter hm2
  have hwm : Measurable w := measurable_w hH c s
  have hset : {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} = {g : G2 | Dt g < 1} := rfl
  have hFm : Measurable (Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w) :=
    hwm.indicator hm1
  have hFl : LInv (Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w) :=
    linv_ind (linv_w hH c s) _
  have hinv : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) ∂μ =
      ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w g ∂μ :=
    (hT (fun g : G2 => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hFm hFl
  have hpt : ∀ g : G2, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) =
      2 ^ (-s) * Set.indicator {g : G2 | Dt g < 2} w g := by
    intro g
    have hD : Dt (dg2 z z * g) = 1 / 2 * Dt g := by rw [Dt_dg, hz2]
    have hwg : w (dg2 z z * g) = 2 ^ (-s) * w g := by
      simp only [hw]
      rw [hH.cen z g, cdet_dg c z hzc' g, cpow_dg, hz2, cpow_half]
      ring
    by_cases h : Dt g < 2
    · have h' : dg2 z z * g ∈ {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} := by
        simp only [Set.mem_setOf_eq, Set.mem_Iio, hD]; linarith
      rw [Set.indicator_of_mem h', Set.indicator_of_mem (show g ∈ {g : G2 | Dt g < 2} from h), hwg]
    · have h' : dg2 z z * g ∉ {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} := by
        simp only [Set.mem_setOf_eq, Set.mem_Iio, hD]; linarith
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (show g ∉ {g : G2 | Dt g < 2} from h),
        mul_zero]
  have e1 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) ∂μ =
      2 ^ (-s) * ∫ g in 𝓕 ∩ {g : G2 | Dt g < 2}, w g ∂μ := by
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_indicator hm2]
  have e2 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w g ∂μ =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
    rw [hset, setIntegral_indicator hm1]
    rfl
  have hun : 𝓕 ∩ {g : G2 | Dt g < 2} = (𝓕 ∩ {g : G2 | Dt g < 1}) ∪ (𝓕 ∩ band) := by
    ext g
    simp only [band, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : Dt g < 1
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, not_lt.1 h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, -, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨h1, h2⟩
  have hdis : Disjoint (𝓕 ∩ {g : G2 | Dt g < 1}) (𝓕 ∩ band) := by
    refine Set.disjoint_left.2 fun g hg hb => ?_
    have h1 : Dt g < 1 := hg.2
    have h2 : 1 ≤ Dt g := hb.2.1
    linarith
  have e3 : ∫ g in 𝓕 ∩ {g : G2 | Dt g < 2}, w g ∂μ =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s + GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s := by
    rw [hun, setIntegral_union hdis (hS.meas.inter hmb) hI (integrableOn_band_w c hS hH s hmb)]
    rfl
  have key : 2 ^ (-s) * (GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s + GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s) =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
    rw [← e3, ← e1, hinv, e2]
  linear_combination -key

end GlobalTheory.CompanionTheory.RSZeta
