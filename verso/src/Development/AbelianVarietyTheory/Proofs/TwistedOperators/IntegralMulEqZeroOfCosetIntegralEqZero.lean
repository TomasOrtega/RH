import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth

open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology Set Filter
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CosetIntegralZero

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]

def cosetAvg (H : Subgroup G) (ν : Measure H) (ψ : G → ℝ) (g : G) : ℝ :=
  ∫ u : H, ψ ((u : G)⁻¹ * g) ∂ν

/- English proof (translation)
Unfold `cosetAvg`. Rewrite using `[← integral_mul_left_eq_self (fun v : H => ψ ((v : G)⁻¹ * ((u : G) * g))) u]`. Use `congr 1`. Use extensionality with `v`. Simplify using `[mul_inv_rev, mul_assoc]`.
-/
theorem cosetAvg_mul [BorelSpace G] [SecondCountableTopology G] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    (ψ : G → ℝ) (u : H) (g : G) : cosetAvg H ν ψ ((u : G) * g) = cosetAvg H ν ψ g := by
  unfold cosetAvg
  rw [← integral_mul_left_eq_self (fun v : H => ψ ((v : G)⁻¹ * ((u : G) * g))) u]
  congr 1; ext v
  simp [mul_inv_rev, mul_assoc]

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Take `⟨t, t_comp, ht⟩` from `exists_compact_mem_nhds x₀`. Establish `hk : IsCompact (((↑) : H → G) ⁻¹' (t • (tsupport ψ)⁻¹))` using `hH.isClosedEmbedding_subtypeVal.isCompact_preimage (t_comp.smul_set hψc.inv)`. Establish `A : ContinuousOn (cosetAvg H ν ψ) t`. Apply `continuousOn_integral_of_compact_support hk` to reduce the goal to its premises.

Conclude with `(hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)).continuousOn`. Introduce `p x hp hx contrapose! hx`. Use `⟨p, hp, p⁻¹ * (x : G), ?_, by simp⟩` and prove the remaining obligations. Simplify `subset_tsupport _ hx` using `only [Set.mem_inv, mul_inv_rev, inv_inv]`. Conclude with `A.continuousAt ht`.
-/
theorem continuous_cosetAvg [LocallyCompactSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [IsFiniteMeasureOnCompacts ν] {ψ : G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Continuous (cosetAvg H ν ψ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨t, t_comp, ht⟩ := exists_compact_mem_nhds x₀
  have hk : IsCompact (((↑) : H → G) ⁻¹' (t • (tsupport ψ)⁻¹)) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage (t_comp.smul_set hψc.inv)
  have A : ContinuousOn (cosetAvg H ν ψ) t := by
    apply continuousOn_integral_of_compact_support hk
    · exact (hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)).continuousOn
    · intro p x hp hx
      contrapose! hx
      refine ⟨p, hp, p⁻¹ * (x : G), ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

/- English proof (translation)
Establish `C : Continuous (fun u : H => ψ ((u : G)⁻¹ * g))` using `by fun_prop`. Apply `(integral_pos_iff_support_of_nonneg (fun u => hψ0 _) ?_).2` to reduce the goal to its premises. Apply `C.isOpen_support.measure_pos ν` to reduce the goal to its premises. Conclude with `⟨1, by simpa using hg⟩`. Apply `C.integrable_of_hasCompactSupport` to reduce the goal to its premises.

Use `HasCompactSupport.intro (hH.isClosedEmbedding_subtypeVal.isCompact_preimage ((show IsCompact (tsupport ψ) from hψc).image (f := fun k => g * k⁻¹) (by fun_prop))) ?_` and prove the remaining obligations. Introduce `u hu`. Assume the negation of the conclusion as `h`. Conclude with `hu ⟨(u : G)⁻¹ * g, subset_tsupport _ h, by simp⟩`.
-/
theorem cosetAvg_pos [BorelSpace G] [SecondCountableTopology G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {ψ : G → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {g : G} (hg : ψ g ≠ 0) : 0 < cosetAvg H ν ψ g := by
  have C : Continuous (fun u : H => ψ ((u : G)⁻¹ * g)) := by fun_prop
  apply (integral_pos_iff_support_of_nonneg (fun u => hψ0 _) ?_).2
  · apply C.isOpen_support.measure_pos ν
    exact ⟨1, by simpa using hg⟩
  · apply C.integrable_of_hasCompactSupport
    refine HasCompactSupport.intro (hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      ((show IsCompact (tsupport ψ) from hψc).image (f := fun k => g * k⁻¹) (by fun_prop))) ?_
    intro u hu
    by_contra h
    exact hu ⟨(u : G)⁻¹ * g, subset_tsupport _ h, by simp⟩

/- English proof (translation)
Establish `hSi : Integrable (S.indicator (fun _ => (1:ℝ))) ν` using `(integrableOn_const hS.measure_ne_top).integrable_indicator hS.measurableSet`. Establish `hMi : Integrable (fun g => C * ‖M.indicator w g‖) μ` using `((hw.integrableOn_isCompact hM).integrable_indicator hM.measurableSet).norm.const_mul C`. Use `(hSi.mul_prod hMi).mono' ?_ (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Conclude with `hP.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_snd`. Take `⟨u, g⟩` from `z`.

Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC (u, g))`. Distinguish the cases in `h : P (u, g) = 0`. Simplify using `only [h, zero_mul, norm_zero]`. Conclude with `mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hC0 (norm_nonneg _))`. Take `⟨hu, hg⟩` from `hPS u g h`.

Simplify using `only [Set.indicator_of_mem hu, Set.indicator_of_mem hg, one_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)`.
-/
theorem integrable_prod_of_bound [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (ν : Measure H) [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    {P : H × G → ℂ} (hP : Continuous P) {C : ℝ} (hC : ∀ z, ‖P z‖ ≤ C) {S : Set H} {M : Set G}
    (hS : IsCompact S) (hM : IsCompact M) (hPS : ∀ u g, P (u, g) ≠ 0 → u ∈ S ∧ g ∈ M)
    {w : G → ℂ} (hw : LocallyIntegrable w μ) :
    Integrable (fun z : H × G => P z * w z.2) (ν.prod μ) := by
  have hSi : Integrable (S.indicator (fun _ => (1:ℝ))) ν :=
    (integrableOn_const hS.measure_ne_top).integrable_indicator hS.measurableSet
  have hMi : Integrable (fun g => C * ‖M.indicator w g‖) μ :=
    ((hw.integrableOn_isCompact hM).integrable_indicator hM.measurableSet).norm.const_mul C
  refine (hSi.mul_prod hMi).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact hP.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_snd
  · obtain ⟨u, g⟩ := z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (u, g))
    by_cases h : P (u, g) = 0
    · simp only [h, zero_mul, norm_zero]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hC0 (norm_nonneg _))
    · obtain ⟨hu, hg⟩ := hPS u g h
      simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hg, one_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

/- English proof (translation)
Take `⟨C, hC⟩` from `hF.bounded_above_of_compact_support hFc`. Establish `hS : IsCompact (((↑) : H → G) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) '' (tsupport F ×ˢ tsupport ψ)))` using `hH.isClosedEmbedding_subtypeVal.isCompact_preimage (((show IsCompact (tsupport F) from hFc).prod (show IsCompact (tsupport ψ) from hψc)).image (by fun_prop))`. Establish `I1 : Integrable (fun z : H × G => ((ψ ((z.1 : G)⁻¹ * z.2) : ℂ) * F z.2) * w z.2) (ν.prod μ)`. Use `integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport F) from hFc) ?_ hw` and prove the remaining obligations. Introduce `z`.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `u g h`. Establish `h1 : ψ ((u : G)⁻¹ * g) ≠ 0` using `fun h' => h (by simp [h'])`. Establish `h2 : F g ≠ 0` using `fun h' => h (by simp [h'])`.

Conclude with `⟨⟨(g, (u : G)⁻¹ * g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h2⟩`. Establish `I2 : Integrable (fun z : H × G => ((ψ z.2 : ℂ) * F ((z.1 : G) * z.2)) * w z.2) (ν.prod μ)`. Use `integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport ψ) from hψc) ?_ hw` and prove the remaining obligations. Introduce `z`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `u g h`. Establish `h1 : ψ g ≠ 0` using `fun h' => h (by simp [h'])`. Establish `h2 : F ((u : G) * g) ≠ 0` using `fun h' => h (by simp [h'])`. Conclude with `⟨⟨((u : G) * g, g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h1⟩`.

Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [cosetAvg, mul_assoc]`. Rewrite using `[integral_mul_const, integral_complex_ofReal]`. Use `_ = ∫ u : H, ∫ g, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂μ ∂ν := (integral_integral_swap (f := fun (u : H) (g : G) => (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g) I1).symm`.

Use `_ = ∫ u : H, ∫ g, (ψ g : ℂ) * F ((u : G) * g) * w g ∂μ ∂ν := by`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only`. Use `conv_lhs => rw [← integral_mul_left_eq_self _ (u : G)]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hinv u u.2] with g hg`. Simplify using `only [inv_mul_cancel_left, hg]`. Use `_ = ∫ g, ∫ u : H, (ψ g : ℂ) * F ((u : G) * g) * w g ∂ν ∂μ := integral_integral_swap (f := fun (u : H) (g : G) => (ψ g : ℂ) * F ((u : G) * g) * w g) I2`. Use `_ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by`. Use `integral_congr_ae (Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use extensionality with `u`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_cosetAvg_mul_eq [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] [SFinite ν]
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] {ψ : G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψ1 : ∀ g, |ψ g| ≤ 1) {F w : G → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hw : LocallyIntegrable w μ) (hinv : ∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) :
    ∫ g, (cosetAvg H ν ψ g : ℂ) * F g * w g ∂μ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hFc
  have hS : IsCompact (((↑) : H → G) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) '' (tsupport F ×ˢ tsupport ψ))) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      (((show IsCompact (tsupport F) from hFc).prod (show IsCompact (tsupport ψ) from hψc)).image (by fun_prop))
  have I1 : Integrable (fun z : H × G => ((ψ ((z.1 : G)⁻¹ * z.2) : ℂ) * F z.2) * w z.2) (ν.prod μ) := by
    refine integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport F) from hFc) ?_ hw
    · intro z
      rw [norm_mul]
      calc _ ≤ 1 * C := mul_le_mul (by simpa using hψ1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · intro u g h
      have h1 : ψ ((u : G)⁻¹ * g) ≠ 0 := fun h' => h (by simp [h'])
      have h2 : F g ≠ 0 := fun h' => h (by simp [h'])
      exact ⟨⟨(g, (u : G)⁻¹ * g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h2⟩
  have I2 : Integrable (fun z : H × G => ((ψ z.2 : ℂ) * F ((z.1 : G) * z.2)) * w z.2) (ν.prod μ) := by
    refine integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport ψ) from hψc) ?_ hw
    · intro z
      rw [norm_mul]
      calc _ ≤ 1 * C := mul_le_mul (by simpa using hψ1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · intro u g h
      have h1 : ψ g ≠ 0 := fun h' => h (by simp [h'])
      have h2 : F ((u : G) * g) ≠ 0 := fun h' => h (by simp [h'])
      exact ⟨⟨((u : G) * g, g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h1⟩
  calc ∫ g, (cosetAvg H ν ψ g : ℂ) * F g * w g ∂μ
      = ∫ g, ∫ u : H, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        simp only [cosetAvg, mul_assoc]
        rw [integral_mul_const, integral_complex_ofReal]
    _ = ∫ u : H, ∫ g, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂μ ∂ν :=
        (integral_integral_swap (f := fun (u : H) (g : G) => (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g) I1).symm
    _ = ∫ u : H, ∫ g, (ψ g : ℂ) * F ((u : G) * g) * w g ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        conv_lhs => rw [← integral_mul_left_eq_self _ (u : G)]
        refine integral_congr_ae ?_
        filter_upwards [hinv u u.2] with g hg
        simp only [inv_mul_cancel_left, hg]
    _ = ∫ g, ∫ u : H, (ψ g : ℂ) * F ((u : G) * g) * w g ∂ν ∂μ :=
        integral_integral_swap (f := fun (u : H) (g : G) => (ψ g : ℂ) * F ((u : G) * g) * w g) I2
    _ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        dsimp only
        rw [← integral_const_mul]
        congr 1; ext u; ring

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ H hH ν _ μ _ f w hf hfc hw hinv hzero`. Use `haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Take `⟨ψ₀, hψ1, -, hψc, hψ01⟩` from `exists_continuous_one_zero_of_isCompact (show IsCompact (tsupport f) from hfc) isClosed_empty (Set.disjoint_empty _)`. Establish `hJc : Continuous (cosetAvg H ν ψ₀)` using `continuous_cosetAvg H hH ν ψ₀.continuous hψc`. Establish `hJpos : ∀ g ∈ tsupport f, 0 < cosetAvg H ν ψ₀ g` using `fun g hg => cosetAvg_pos H hH ν ψ₀.continuous hψc (fun x => (hψ01 x).1) (by rw [hψ1 hg]; simp)`.

Use `set F : G → ℂ := fun g => f g / (cosetAvg H ν ψ₀ g : ℂ) with hFdef`. Establish `hF : Continuous F`. Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ tsupport f`. Conclude with `hf.continuousAt.div (Complex.continuous_ofReal.comp hJc).continuousAt (by exact_mod_cast (hJpos g hg).ne')`.

Establish `: F =ᶠ[𝓝 g] fun _ => 0` using `by filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hg] with x hx`. Simplify using `[hFdef, image_eq_zero_of_notMem_tsupport hx]`. Conclude with `continuousAt_const.congr this.symm`. Establish `hFc : HasCompactSupport F` using `hfc.mono fun g hg h => hg (by simp [hFdef, h])`. Establish `hFJ : ∀ g, (cosetAvg H ν ψ₀ g : ℂ) * F g * w g = f g * w g`.

Introduce `g`. Distinguish the cases in `h : f g = 0`. Simplify using `[hFdef, h]`. Establish `hJ : (cosetAvg H ν ψ₀ g : ℂ) ≠ 0` using `by exact_mod_cast (hJpos g (subset_tsupport _ h)).ne'`. Rewrite using `[hFdef, mul_div_cancel₀ _ hJ]`.

Establish `hFH : ∀ g, ∫ u : H, F ((u : G) * g) ∂ν = 0`. Introduce `g`. Simplify using `only [hFdef, cosetAvg_mul H ν ψ₀ _ g]`. Rewrite using `[integral_div, hzero g, zero_div]`. Apply the tactic sequence `have key := integral_cosetAvg_mul_eq H hH ν μ ψ₀.continuous hψc (fun g => by rw [abs_le]; constructor <;> linarith [(hψ01 g).1, (hψ01 g).2]) hF hFc hw hinv`.

Simplify using `only [hFJ, hFH, mul_zero, integral_zero] at key`. Conclude with `key`.
-/
theorem integral_mul_eq_zero_of_coset_integral_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure]
    (μ : Measure G) [μ.IsHaarMeasure] (f w : G → ℂ), Continuous f → HasCompactSupport f →
    LocallyIntegrable w μ → (∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) →
    (∀ g, ∫ u : H, f (u * g) ∂ν = 0) → ∫ g, f g * w g ∂μ = 0 := by
  intro G _ _ _ _ _ _ _ _ H hH ν _ μ _ f w hf hfc hw hinv hzero
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨ψ₀, hψ1, -, hψc, hψ01⟩ := exists_continuous_one_zero_of_isCompact
    (show IsCompact (tsupport f) from hfc) isClosed_empty (Set.disjoint_empty _)
  have hJc : Continuous (cosetAvg H ν ψ₀) := continuous_cosetAvg H hH ν ψ₀.continuous hψc
  have hJpos : ∀ g ∈ tsupport f, 0 < cosetAvg H ν ψ₀ g := fun g hg =>
    cosetAvg_pos H hH ν ψ₀.continuous hψc (fun x => (hψ01 x).1) (by rw [hψ1 hg]; simp)
  set F : G → ℂ := fun g => f g / (cosetAvg H ν ψ₀ g : ℂ) with hFdef
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    by_cases hg : g ∈ tsupport f
    · exact hf.continuousAt.div (Complex.continuous_ofReal.comp hJc).continuousAt
        (by exact_mod_cast (hJpos g hg).ne')
    · have : F =ᶠ[𝓝 g] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hg] with x hx
        simp [hFdef, image_eq_zero_of_notMem_tsupport hx]
      exact continuousAt_const.congr this.symm
  have hFc : HasCompactSupport F :=
    hfc.mono fun g hg h => hg (by simp [hFdef, h])
  have hFJ : ∀ g, (cosetAvg H ν ψ₀ g : ℂ) * F g * w g = f g * w g := by
    intro g
    by_cases h : f g = 0
    · simp [hFdef, h]
    · have hJ : (cosetAvg H ν ψ₀ g : ℂ) ≠ 0 := by exact_mod_cast (hJpos g (subset_tsupport _ h)).ne'
      rw [hFdef, mul_div_cancel₀ _ hJ]
  have hFH : ∀ g, ∫ u : H, F ((u : G) * g) ∂ν = 0 := by
    intro g
    simp only [hFdef, cosetAvg_mul H ν ψ₀ _ g]
    rw [integral_div, hzero g, zero_div]
  have key := integral_cosetAvg_mul_eq H hH ν μ ψ₀.continuous hψc
    (fun g => by rw [abs_le]; constructor <;> linarith [(hψ01 g).1, (hψ01 g).2]) hF hFc hw hinv
  simp only [hFJ, hFH, mul_zero, integral_zero] at key
  exact key

end GlobalTheory.CosetIntegralZero
