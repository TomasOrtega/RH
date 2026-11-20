import Mathlib
import GroundTheory.AutomorphicForms.QuotientKernel
import GroundTheory.AutomorphicForms.TraceFormulaConvolution

open MeasureTheory Set Filter Topology Function
open scoped ENNReal Pointwise InnerProductSpace ComplexConjugate

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

section HilbertSchmidt

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Use `set b := stdHilbertBasis ℂ H`. Establish `hpt : ∀ x, ∑' i, ‖e x (b i)‖ₑ ^ 2 ≤ ENNReal.ofReal B ^ 2`. Introduce `x`. Use `set k := (InnerProductSpace.toDual ℂ H).symm (e x)`. Establish `hk : ∀ w, e x w = ⟪k, w⟫_ℂ` using `fun w => (InnerProductSpace.toDual_symm_apply).symm`.

Establish `hkn : ‖k‖ = ‖e x‖` using `LinearIsometryEquiv.norm_map _ _`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `i`. Rewrite using `[hk, enorm_inner_comm]`.

Use `_ = ‖k‖ₑ ^ 2 := (enorm_sq_eq_tsum b k).symm`. Use `_ ≤ ENNReal.ofReal B ^ 2 := by gcongr`. Rewrite using `[← ofReal_norm, hkn]`. Conclude with `ENNReal.ofReal_le_ofReal (hB x)`. Establish `hmeas : ∀ i, AEMeasurable (fun x => ‖e x (b i)‖ₑ ^ 2) ν` using `fun i => ((Lp.aestronglyMeasurable (T (b i))).enorm.pow_const 2).congr ((hT (b i)).mono fun x hx => by simp only [hx])`.

Unfold `IsHilbertSchmidt`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `i`. Rewrite using `[Lp.enorm_def, L2Kernel.eLpNorm_two_sq]`.

Conclude with `lintegral_congr_ae ((hT (b i)).mono fun x hx => by simp only [hx])`. Use `_ ≤ ∫⁻ x, ∑' i, ‖e x (b i)‖ₑ ^ 2 ∂ν := by`. Rewrite using `[ENNReal.tsum_eq_iSup_sum]`. Use `iSup_le fun F => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_finsetSum' F fun i _ => hmeas i]`.

Conclude with `lintegral_mono fun x => ENNReal.sum_le_tsum F`. Use `_ ≤ ∫⁻ _, ENNReal.ofReal B ^ 2 ∂ν := lintegral_mono hpt`. Use `_ < ⊤ := by`. Rewrite using `[lintegral_const]`. Conclude with `ENNReal.mul_lt_top (by simp) (measure_lt_top ν univ)`.
-/
theorem isHilbertSchmidt_of_ae_eq_dual (T : H →L[ℂ] Lp ℂ 2 ν) (e : X → StrongDual ℂ H) (B : ℝ)
    (hB : ∀ x, ‖e x‖ ≤ B) (hT : ∀ v, T v =ᵐ[ν] fun x => e x v) : IsHilbertSchmidt T := by
  set b := stdHilbertBasis ℂ H
  have hpt : ∀ x, ∑' i, ‖e x (b i)‖ₑ ^ 2 ≤ ENNReal.ofReal B ^ 2 := by
    intro x
    set k := (InnerProductSpace.toDual ℂ H).symm (e x)
    have hk : ∀ w, e x w = ⟪k, w⟫_ℂ := fun w => (InnerProductSpace.toDual_symm_apply).symm
    have hkn : ‖k‖ = ‖e x‖ := LinearIsometryEquiv.norm_map _ _
    calc ∑' i, ‖e x (b i)‖ₑ ^ 2 = ∑' i, ‖⟪b i, k⟫_ℂ‖ₑ ^ 2 := by
          congr 1; ext i; rw [hk, enorm_inner_comm]
      _ = ‖k‖ₑ ^ 2 := (enorm_sq_eq_tsum b k).symm
      _ ≤ ENNReal.ofReal B ^ 2 := by
          gcongr
          rw [← ofReal_norm, hkn]
          exact ENNReal.ofReal_le_ofReal (hB x)
  have hmeas : ∀ i, AEMeasurable (fun x => ‖e x (b i)‖ₑ ^ 2) ν := fun i =>
    ((Lp.aestronglyMeasurable (T (b i))).enorm.pow_const 2).congr
      ((hT (b i)).mono fun x hx => by simp only [hx])
  unfold IsHilbertSchmidt
  calc hsNormSq T = ∑' i, ‖T (b i)‖ₑ ^ 2 := rfl
    _ = ∑' i, ∫⁻ x, ‖e x (b i)‖ₑ ^ 2 ∂ν := by
        congr 1; ext i
        rw [Lp.enorm_def, L2Kernel.eLpNorm_two_sq]
        exact lintegral_congr_ae ((hT (b i)).mono fun x hx => by simp only [hx])
    _ ≤ ∫⁻ x, ∑' i, ‖e x (b i)‖ₑ ^ 2 ∂ν := by
        rw [ENNReal.tsum_eq_iSup_sum]
        refine iSup_le fun F => ?_
        rw [← lintegral_finsetSum' F fun i _ => hmeas i]
        exact lintegral_mono fun x => ENNReal.sum_le_tsum F
    _ ≤ ∫⁻ _, ENNReal.ofReal B ^ 2 ∂ν := lintegral_mono hpt
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (by simp) (measure_lt_top ν univ)

end HilbertSchmidt

/- English proof (translation)
Establish `h' : ‖z‖ ^ 2 ≤ A.toReal * ‖v‖ ^ 2`. Use `ENNReal.toReal_mono (ENNReal.mul_ne_top hA (by simp)) h` as an intermediate fact. Simplify `this` using `[ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm]`. Rewrite using `[← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul ENNReal.toReal_nonneg]`. Conclude with `Real.sqrt_le_sqrt h'`.
-/
theorem norm_le_of_enorm_sq_le {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {z : E} {v : F} {A : ℝ≥0∞} (hA : A ≠ ⊤) (h : ‖z‖ₑ ^ 2 ≤ A * ‖v‖ₑ ^ 2) :
    ‖z‖ ≤ √A.toReal * ‖v‖ := by
  have h' : ‖z‖ ^ 2 ≤ A.toReal * ‖v‖ ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hA (by simp)) h
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm] using this
  rw [← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul
    ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h'

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

omit [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in

/- English proof (translation)
Establish `hfin` using `finite_setOf_mem_of_isCompact Γ (hC.mul hC.inv)`. Use `⟨hfin.toFinset.card, fun g => ?_⟩` and prove the remaining obligations. Break down `eq_empty_or_nonempty {γ : Γ | γ • g ∈ C} with h | ⟨γ₀, hγ₀⟩` into its components or cases. Rewrite using `[h, encard_empty]`. Simplify using the standard rewrite rules.

Establish `hsub : (fun γ : Γ => γ * γ₀⁻¹) '' {γ : Γ | γ • g ∈ C} ⊆ {δ : Γ | (δ : G) ∈ C * C⁻¹}`. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Use `⟨γ • g, hγ, (γ₀ • g)⁻¹, Set.inv_mem_inv.2 hγ₀, ?_⟩` and prove the remaining obligations. Simplify using `only [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_encard_le_of_isCompact {C : Set G} (hC : IsCompact C) :
    ∃ N : ℕ, ∀ g : G, {γ : Γ | γ • g ∈ C}.encard ≤ N := by
  have hfin := finite_setOf_mem_of_isCompact Γ (hC.mul hC.inv)
  refine ⟨hfin.toFinset.card, fun g => ?_⟩
  rcases eq_empty_or_nonempty {γ : Γ | γ • g ∈ C} with h | ⟨γ₀, hγ₀⟩
  · rw [h, encard_empty]; simp
  have hsub : (fun γ : Γ => γ * γ₀⁻¹) '' {γ : Γ | γ • g ∈ C} ⊆ {δ : Γ | (δ : G) ∈ C * C⁻¹} := by
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨γ • g, hγ, (γ₀ • g)⁻¹, Set.inv_mem_inv.2 hγ₀, ?_⟩
    simp only [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc {γ : Γ | γ • g ∈ C}.encard
      = ((fun γ : Γ => γ * γ₀⁻¹) '' {γ : Γ | γ • g ∈ C}).encard :=
        ((mul_left_injective γ₀⁻¹).injOn).encard_image.symm
    _ ≤ {δ : Γ | (δ : G) ∈ C * C⁻¹}.encard := encard_le_encard hsub
    _ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card

variable (μ : Measure G) [μ.IsMulLeftInvariant]

/- English proof (translation)
Rewrite using `[← lintegral_indicator hE, lintegral_eq_lintegral_automorphize (Γ := Γ) μ (f := E.indicator fun g => h (mk Γ g)) ((hh.comp (measurable_mk Γ)).indicator hE).aemeasurable, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `mk_surjective Γ x`. Express the relevant statement in the definitionally equal form `∑' γ : Γ, E.indicator (fun g => h (mk Γ g)) (γ • g) ≤ N * h (mk Γ g)`. Establish `hrw : ∀ γ : Γ, E.indicator (fun g => h (mk Γ g)) (γ • g) = {γ : Γ | γ • g ∈ E}.indicator (fun _ => h (mk Γ g)) γ`.

Introduce `γ`. Distinguish the cases in `hγ : γ • g ∈ E`. Rewrite using `[indicator_of_mem hγ, indicator_of_mem (show γ ∈ {γ : Γ | γ • g ∈ E} from hγ), mk_smul]`. Rewrite using `[indicator_of_notMem hγ, indicator_of_notMem (show γ ∉ {γ : Γ | γ • g ∈ E} from hγ)]`. Repeatedly rewrite using `[hrw]`.

Rewrite using `[← tsum_subtype, ENNReal.tsum_set_const]`. Use `gcongr`. Use `hN g` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem lintegral_indicator_le {E : Set G} (hE : MeasurableSet E) {N : ℕ}
    (hN : ∀ g : G, {γ : Γ | γ • g ∈ E}.encard ≤ N) {h : RightCosetSpace Γ → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ g in E, h (mk Γ g) ∂μ ≤ N * ∫⁻ x, h x ∂quotientMeasure Γ μ := by
  rw [← lintegral_indicator hE, lintegral_eq_lintegral_automorphize (Γ := Γ) μ
    (f := E.indicator fun g => h (mk Γ g)) ((hh.comp (measurable_mk Γ)).indicator hE).aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
  refine lintegral_mono fun x => ?_
  obtain ⟨g, rfl⟩ := mk_surjective Γ x
  change ∑' γ : Γ, E.indicator (fun g => h (mk Γ g)) (γ • g) ≤ N * h (mk Γ g)
  have hrw : ∀ γ : Γ, E.indicator (fun g => h (mk Γ g)) (γ • g) =
      {γ : Γ | γ • g ∈ E}.indicator (fun _ => h (mk Γ g)) γ := by
    intro γ
    by_cases hγ : γ • g ∈ E
    · rw [indicator_of_mem hγ, indicator_of_mem (show γ ∈ {γ : Γ | γ • g ∈ E} from hγ), mk_smul]
    · rw [indicator_of_notMem hγ, indicator_of_notMem (show γ ∉ {γ : Γ | γ • g ∈ E} from hγ)]
  simp_rw [hrw]
  rw [← tsum_subtype, ENNReal.tsum_set_const]
  gcongr
  have := hN g
  exact_mod_cast this

/- English proof (translation)
Use `⟨measurable_mk Γ, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply (measurable_mk Γ) hs]`. Establish `hs' : MeasurableSet (mk Γ ⁻¹' s)` using `hs.preimage (measurable_mk Γ)`. Rewrite using `[← lintegral_indicator_one hs', lintegral_eq_lintegral_automorphize (Γ := Γ) μ (f := (mk Γ ⁻¹' s).indicator 1) (measurable_one.indicator hs').aemeasurable]`. Use `nonpos_iff_eq_zero.1 ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `mk_surjective Γ x`. Distinguish the cases in `hx : mk Γ g ∈ s`. Rewrite using `[indicator_of_mem hx]`.

Conclude with `le_top`. Express the relevant statement in the definitionally equal form `∑' γ : Γ, (mk Γ ⁻¹' s).indicator 1 (γ • g) ≤ _`. Establish `: ∀ γ : Γ, (mk Γ ⁻¹' s).indicator (1 : G → ℝ≥0∞) (γ • g) = 0` using `fun γ => indicator_of_notMem (by simpa [mk_smul] using hx) _`. Simplify using `[this]`. Use `_ = 0 := by rw [lintegral_indicator_const hs, h0, mul_zero]`.
-/
theorem quasiMeasurePreserving_mk :
    Measure.QuasiMeasurePreserving (mk Γ) μ (quotientMeasure Γ μ) := by
  refine ⟨measurable_mk Γ, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply (measurable_mk Γ) hs]
  have hs' : MeasurableSet (mk Γ ⁻¹' s) := hs.preimage (measurable_mk Γ)
  rw [← lintegral_indicator_one hs', lintegral_eq_lintegral_automorphize (Γ := Γ) μ
    (f := (mk Γ ⁻¹' s).indicator 1) (measurable_one.indicator hs').aemeasurable]
  refine nonpos_iff_eq_zero.1 ?_
  calc ∫⁻ x, MulAction.automorphize ((mk Γ ⁻¹' s).indicator 1) x ∂quotientMeasure Γ μ
      ≤ ∫⁻ x, s.indicator (fun _ => ⊤) x ∂quotientMeasure Γ μ := by
        refine lintegral_mono fun x => ?_
        obtain ⟨g, rfl⟩ := mk_surjective Γ x
        by_cases hx : mk Γ g ∈ s
        · rw [indicator_of_mem hx]; exact le_top
        · change ∑' γ : Γ, (mk Γ ⁻¹' s).indicator 1 (γ • g) ≤ _
          have : ∀ γ : Γ, (mk Γ ⁻¹' s).indicator (1 : G → ℝ≥0∞) (γ • g) = 0 := fun γ =>
            indicator_of_notMem (by simpa [mk_smul] using hx) _
          simp [this]
    _ = 0 := by rw [lintegral_indicator_const hs, h0, mul_zero]

/- English proof (translation)
The claim follows from `(Lp.stronglyMeasurable φ).comp_measurable (measurable_mk Γ)`.
-/
theorem stronglyMeasurable_lift (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    StronglyMeasurable fun g => φ (mk Γ g) :=
  (Lp.stronglyMeasurable φ).comp_measurable (measurable_mk Γ)

/- English proof (translation)
Rewrite using `[Lp.enorm_def, L2Kernel.eLpNorm_two_sq]`. Conclude with `lintegral_indicator_le Γ μ hE hN ((Lp.stronglyMeasurable φ).measurable.enorm.pow_const 2)`.
-/
theorem lintegral_lift_sq_le (φ : Lp ℂ 2 (quotientMeasure Γ μ)) {E : Set G} (hE : MeasurableSet E)
    {N : ℕ} (hN : ∀ g : G, {γ : Γ | γ • g ∈ E}.encard ≤ N) :
    ∫⁻ g in E, ‖φ (mk Γ g)‖ₑ ^ 2 ∂μ ≤ N * ‖φ‖ₑ ^ 2 := by
  rw [Lp.enorm_def, L2Kernel.eLpNorm_two_sq]
  exact lintegral_indicator_le Γ μ hE hN
    ((Lp.stronglyMeasurable φ).measurable.enorm.pow_const 2)

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_encard_le_of_isCompact Γ hC`. Use `(lintegral_lift_sq_le Γ μ φ hC.measurableSet hN).trans_lt ?_` and prove the remaining obligations. Conclude with `ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top enorm_lt_top)`.
-/
theorem lintegral_lift_sq_lt_top (φ : Lp ℂ 2 (quotientMeasure Γ μ)) {C : Set G} (hC : IsCompact C) :
    ∫⁻ g in C, ‖φ (mk Γ g)‖ₑ ^ 2 ∂μ < ⊤ := by
  obtain ⟨N, hN⟩ := exists_encard_le_of_isCompact Γ hC
  refine (lintegral_lift_sq_le Γ μ φ hC.measurableSet hN).trans_lt ?_
  exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top enorm_lt_top)

variable [IsFiniteMeasureOnCompacts μ]

/- English proof (translation)
Establish `hm : MemLp (fun g => φ (mk Γ g)) 2 (μ.restrict C)`. Use `⟨(stronglyMeasurable_lift Γ μ φ).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `L2Kernel.lt_top_of_sq_lt_top ?_` and prove the remaining obligations. Rewrite using `[L2Kernel.eLpNorm_two_sq]`. Conclude with `lintegral_lift_sq_lt_top Γ μ φ hC`.

Establish `: IsFiniteMeasure (μ.restrict C)` using `⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩`. Conclude with `hm.integrable one_le_two`.
-/
theorem integrableOn_lift (φ : Lp ℂ 2 (quotientMeasure Γ μ)) {C : Set G} (hC : IsCompact C) :
    IntegrableOn (fun g => φ (mk Γ g)) C μ := by
  have hm : MemLp (fun g => φ (mk Γ g)) 2 (μ.restrict C) := by
    refine ⟨(stronglyMeasurable_lift Γ μ φ).aestronglyMeasurable, ?_⟩
    refine L2Kernel.lt_top_of_sq_lt_top ?_
    rw [L2Kernel.eLpNorm_two_sq]
    exact lintegral_lift_sq_lt_top Γ μ φ hC
  have : IsFiniteMeasure (μ.restrict C) := ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  exact hm.integrable one_le_two

def rconv (f : G → ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) : ℂ :=
  ∫ y, f (x⁻¹ * y) * φ (mk Γ y) ∂μ

/- English proof (translation)
Establish `hC : IsCompact ((x * ·) '' tsupport (f : G → ℂ))` using `f.hasCompactSupport.isCompact.image (continuous_const_mul x)`. Establish `hzero : ∀ y ∉ (x * ·) '' tsupport (f : G → ℂ), f (x⁻¹ * y) * φ (mk Γ y) = 0`. Introduce `y hy`. Establish `: x⁻¹ * y ∉ tsupport (f : G → ℂ)` using `fun h => hy ⟨x⁻¹ * y, h, by simp⟩`. Simplify using `[image_eq_zero_of_notMem_tsupport this]`.

Use `IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hzero` and prove the remaining obligations. Take `⟨M, hM⟩` from `f.continuous.bounded_above_of_compact_support f.hasCompactSupport`. Conclude with `(integrableOn_lift Γ μ φ hC).bdd_mul (f.continuous.comp (continuous_const_mul x⁻¹)).aestronglyMeasurable (Eventually.of_forall fun y => hM _)`.
-/
theorem integrable_rconv (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) :
    Integrable (fun y => f (x⁻¹ * y) * φ (mk Γ y)) μ := by
  have hC : IsCompact ((x * ·) '' tsupport (f : G → ℂ)) :=
    f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  have hzero : ∀ y ∉ (x * ·) '' tsupport (f : G → ℂ), f (x⁻¹ * y) * φ (mk Γ y) = 0 := by
    intro y hy
    have : x⁻¹ * y ∉ tsupport (f : G → ℂ) := fun h => hy ⟨x⁻¹ * y, h, by simp⟩
    simp [image_eq_zero_of_notMem_tsupport this]
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hzero
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  exact (integrableOn_lift Γ μ φ hC).bdd_mul
    (f.continuous.comp (continuous_const_mul x⁻¹)).aestronglyMeasurable
    (Eventually.of_forall fun y => hM _)

/- English proof (translation)
Unfold `rconv`. Rewrite using `[← integral_mul_left_eq_self (fun y => f ((γ * x)⁻¹ * y) * φ (mk Γ y)) γ]`. Use `congr 1`. Use extensionality with `y`. Rewrite using `[mul_inv_rev, mul_assoc, inv_mul_cancel_left, mk_mul_of_mem hγ]`.
-/
theorem rconv_mul_left (f : G → ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) {γ : G} (hγ : γ ∈ Γ)
    (x : G) : rconv Γ μ f φ (γ * x) = rconv Γ μ f φ x := by
  unfold rconv
  rw [← integral_mul_left_eq_self (fun y => f ((γ * x)⁻¹ * y) * φ (mk Γ y)) γ]
  congr 1
  ext y
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mk_mul_of_mem hγ]

/- English proof (translation)
Unfold `rconv`. Rewrite using `[← integral_add (integrable_rconv Γ μ f φ x) (integrable_rconv Γ μ f ψ x)]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [(quasiMeasurePreserving_mk Γ μ).ae_eq_comp (Lp.coeFn_add φ ψ)] with y hy`. Simplify using `only [comp_apply, Pi.add_apply] at hy`.

Rewrite using `[hy, mul_add]`.
-/
theorem rconv_add (f : CompactlySupportedContinuousMap G ℂ) (φ ψ : Lp ℂ 2 (quotientMeasure Γ μ))
    (x : G) : rconv Γ μ f (φ + ψ) x = rconv Γ μ f φ x + rconv Γ μ f ψ x := by
  unfold rconv
  rw [← integral_add (integrable_rconv Γ μ f φ x) (integrable_rconv Γ μ f ψ x)]
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_mk Γ μ).ae_eq_comp (Lp.coeFn_add φ ψ)] with y hy
  simp only [comp_apply, Pi.add_apply] at hy
  rw [hy, mul_add]

/- English proof (translation)
Unfold `rconv`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [(quasiMeasurePreserving_mk Γ μ).ae_eq_comp (Lp.coeFn_smul c φ)] with y hy`. Simplify using `only [comp_apply, Pi.smul_apply, smul_eq_mul] at hy`.

Rewrite using `[hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rconv_smul (f : CompactlySupportedContinuousMap G ℂ) (c : ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) :
    rconv Γ μ f (c • φ) x = c * rconv Γ μ f φ x := by
  unfold rconv
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_mk Γ μ).ae_eq_comp (Lp.coeFn_smul c φ)] with y hy
  simp only [comp_apply, Pi.smul_apply, smul_eq_mul] at hy
  rw [hy]
  ring

/- English proof (translation)
Establish `hm1 : AEMeasurable (fun y => ‖f (x⁻¹ * y)‖ₑ) μ` using `(f.continuous.comp (continuous_const_mul x⁻¹)).measurable.enorm.aemeasurable`. Establish `hm2 : AEMeasurable (S.indicator fun y => ‖φ (mk Γ y)‖ₑ) μ` using `((stronglyMeasurable_lift Γ μ φ).measurable.enorm.indicator hS).aemeasurable`. Combine the equalities or inequalities in the displayed calculation. Use `(enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`.

Use extensionality with `y`. Distinguish the cases in `hy : y ∈ S`. Rewrite using `[indicator_of_mem hy, enorm_mul]`. Rewrite using `[indicator_of_notMem hy, hfS y hy]`. Simplify using the standard rewrite rules.

Use `_ ≤ (∫⁻ y, ‖f (x⁻¹ * y)‖ₑ ^ 2 ∂μ) * ∫⁻ y, S.indicator (fun y => ‖φ (mk Γ y)‖ₑ) y ^ 2 ∂μ := L2Kernel.lintegral_mul_sq_le μ hm1 hm2`. Use `_ = (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) * ∫⁻ y in S, ‖φ (mk Γ y)‖ₑ ^ 2 ∂μ := by`. Use `congr 1`. Conclude with `lintegral_mul_left_eq_self (fun y => ‖f y‖ₑ ^ 2) x⁻¹`. Rewrite using `[← lintegral_indicator hS]`.

Use `congr 1`. Use extensionality with `y`. Distinguish the cases in `hy : y ∈ S`. Simplify using `[hy]`. Simplify using `[hy]`.

Use `_ ≤ _ := by gcongr`. Conclude with `lintegral_lift_sq_le Γ μ φ hS hN`.
-/
theorem enorm_rconv_sq_le (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) {S : Set G} (hS : MeasurableSet S)
    (hfS : ∀ y ∉ S, f (x⁻¹ * y) = 0) {N : ℕ} (hN : ∀ g : G, {γ : Γ | γ • g ∈ S}.encard ≤ N) :
    ‖rconv Γ μ f φ x‖ₑ ^ 2 ≤ (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) * (N * ‖φ‖ₑ ^ 2) := by
  have hm1 : AEMeasurable (fun y => ‖f (x⁻¹ * y)‖ₑ) μ :=
    (f.continuous.comp (continuous_const_mul x⁻¹)).measurable.enorm.aemeasurable
  have hm2 : AEMeasurable (S.indicator fun y => ‖φ (mk Γ y)‖ₑ) μ :=
    ((stronglyMeasurable_lift Γ μ φ).measurable.enorm.indicator hS).aemeasurable
  calc ‖rconv Γ μ f φ x‖ₑ ^ 2
      ≤ (∫⁻ y, ‖f (x⁻¹ * y)‖ₑ * S.indicator (fun y => ‖φ (mk Γ y)‖ₑ) y ∂μ) ^ 2 := by
        gcongr
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1
        ext y
        by_cases hy : y ∈ S
        · rw [indicator_of_mem hy, enorm_mul]
        · rw [indicator_of_notMem hy, hfS y hy]
          simp
    _ ≤ (∫⁻ y, ‖f (x⁻¹ * y)‖ₑ ^ 2 ∂μ) *
          ∫⁻ y, S.indicator (fun y => ‖φ (mk Γ y)‖ₑ) y ^ 2 ∂μ :=
        L2Kernel.lintegral_mul_sq_le μ hm1 hm2
    _ = (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) * ∫⁻ y in S, ‖φ (mk Γ y)‖ₑ ^ 2 ∂μ := by
        congr 1
        · exact lintegral_mul_left_eq_self (fun y => ‖f y‖ₑ ^ 2) x⁻¹
        · rw [← lintegral_indicator hS]
          congr 1
          ext y
          by_cases hy : y ∈ S
          · simp [hy]
          · simp [hy]
    _ ≤ _ := by
        gcongr
        exact lintegral_lift_sq_le Γ μ φ hS hN

/- English proof (translation)
Establish `hC : IsCompact ((x * ·) '' tsupport (f : G → ℂ))` using `f.hasCompactSupport.isCompact.image (continuous_const_mul x)`. Take `⟨N, hN⟩` from `exists_encard_le_of_isCompact Γ hC`. Establish `hf2 : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤`. Use `(f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) f.hasCompactSupport).2` as an intermediate fact. Rewrite using `[← L2Kernel.eLpNorm_two_sq]`.

Conclude with `(ENNReal.pow_lt_top this).ne`. Use `⟨√((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) * N).toReal, fun φ => ?_⟩` and prove the remaining obligations. Use `norm_le_of_enorm_sq_le (ENNReal.mul_ne_top hf2 (by simp)) ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `enorm_rconv_sq_le Γ μ f φ x hC.measurableSet (fun y hy => ?_) hN` and prove the remaining obligations.

Establish `: x⁻¹ * y ∉ tsupport (f : G → ℂ)` using `fun h => hy ⟨x⁻¹ * y, h, by simp⟩`. Conclude with `image_eq_zero_of_notMem_tsupport this`.
-/
theorem exists_norm_rconv_le (f : CompactlySupportedContinuousMap G ℂ) (x : G) :
    ∃ C : ℝ, ∀ φ : Lp ℂ 2 (quotientMeasure Γ μ), ‖rconv Γ μ f φ x‖ ≤ C * ‖φ‖ := by
  have hC : IsCompact ((x * ·) '' tsupport (f : G → ℂ)) :=
    f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  obtain ⟨N, hN⟩ := exists_encard_le_of_isCompact Γ hC
  have hf2 : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have := (f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) f.hasCompactSupport).2
    rw [← L2Kernel.eLpNorm_two_sq]
    exact (ENNReal.pow_lt_top this).ne
  refine ⟨√((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) * N).toReal, fun φ => ?_⟩
  refine norm_le_of_enorm_sq_le (ENNReal.mul_ne_top hf2 (by simp)) ?_
  rw [mul_assoc]
  refine enorm_rconv_sq_le Γ μ f φ x hC.measurableSet (fun y hy => ?_) hN
  have : x⁻¹ * y ∉ tsupport (f : G → ℂ) := fun h => hy ⟨x⁻¹ * y, h, by simp⟩
  exact image_eq_zero_of_notMem_tsupport this

def rconvCLM (f : CompactlySupportedContinuousMap G ℂ) (x : G) :
    StrongDual ℂ (Lp ℂ 2 (quotientMeasure Γ μ)) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun φ => rconv Γ μ f φ x
      map_add' := fun φ ψ => rconv_add Γ μ f φ ψ x
      map_smul' := fun c φ => rconv_smul Γ μ f c φ x }
    (exists_norm_rconv_le Γ μ f x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem rconvCLM_apply (f : CompactlySupportedContinuousMap G ℂ) (x : G)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) : rconvCLM Γ μ f x φ = rconv Γ μ f φ x :=
  rfl

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Take `⟨V, hVc, hV⟩` from `exists_compact_mem_nhds x₀`. Establish `hS : IsCompact (V * tsupport (f : G → ℂ))` using `hVc.mul f.hasCompactSupport`. Take `⟨M, hM⟩` from `f.continuous.bounded_above_of_compact_support f.hasCompactSupport`. Use `continuousAt_of_dominated (bound := (V * tsupport (f : G → ℂ)).indicator fun y => M * ‖φ (mk Γ y)‖) (Eventually.of_forall fun x => (integrable_rconv Γ μ f φ x).aestronglyMeasurable) ?_ ?_ ?_` and prove the remaining obligations.

Use `filter_upwards [hV] with x hx`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ V * tsupport (f : G → ℂ)`. Rewrite using `[indicator_of_mem hy, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)`.

Establish `: x⁻¹ * y ∉ tsupport (f : G → ℂ)` using `fun h => hy ⟨x, hx, x⁻¹ * y, h, by simp⟩`. Rewrite using `[indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport this, zero_mul, norm_zero]`. Conclude with `(show IntegrableOn (fun y => M * ‖φ (mk Γ y)‖) (V * tsupport (f : G → ℂ)) μ from (integrableOn_lift Γ μ φ hS).norm.const_mul M).integrable_indicator hS.measurableSet`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Conclude with `((f.continuous.comp ((continuous_inv.comp continuous_id).mul continuous_const)).mul continuous_const).continuousAt`.
-/
theorem continuous_rconv (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) : Continuous (rconv Γ μ f φ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds x₀
  have hS : IsCompact (V * tsupport (f : G → ℂ)) := hVc.mul f.hasCompactSupport
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  refine continuousAt_of_dominated
    (bound := (V * tsupport (f : G → ℂ)).indicator fun y => M * ‖φ (mk Γ y)‖)
    (Eventually.of_forall fun x => (integrable_rconv Γ μ f φ x).aestronglyMeasurable) ?_ ?_ ?_
  · filter_upwards [hV] with x hx
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ V * tsupport (f : G → ℂ)
    · rw [indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · have : x⁻¹ * y ∉ tsupport (f : G → ℂ) := fun h => hy ⟨x, hx, x⁻¹ * y, h, by simp⟩
      rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport this, zero_mul, norm_zero]
  · exact (show IntegrableOn (fun y => M * ‖φ (mk Γ y)‖) (V * tsupport (f : G → ℂ)) μ from
      (integrableOn_lift Γ μ φ hS).norm.const_mul M).integrable_indicator hS.measurableSet
  · refine Eventually.of_forall fun y => ?_
    exact ((f.continuous.comp ((continuous_inv.comp continuous_id).mul continuous_const)).mul
      continuous_const).continuousAt

def rconvQ (f : CompactlySupportedContinuousMap G ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    RightCosetSpace Γ → ℂ :=
  Quotient.lift (rconv Γ μ f φ) fun a b hab => by
    obtain ⟨γ, rfl⟩ := hab
    exact rconv_mul_left Γ μ f φ γ.2 b

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem rconvQ_mk (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : G) : rconvQ Γ μ f φ (mk Γ x) = rconv Γ μ f φ x :=
  rfl

/- English proof (translation)
The claim follows from `(isOpenQuotientMap_mk Γ).isQuotientMap.continuous_iff.2 (continuous_rconv Γ μ f φ)`.
-/
theorem continuous_rconvQ (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) : Continuous (rconvQ Γ μ f φ) :=
  (isOpenQuotientMap_mk Γ).isQuotientMap.continuous_iff.2 (continuous_rconv Γ μ f φ)

section Operator

variable [μ.IsMulRightInvariant] [IsFiniteMeasure (quotientMeasure Γ μ)]

/- English proof (translation)
Establish `hcont : Continuous fun p : G × RightCosetSpace Γ => rightMul Γ p.1 p.2` using `(continuous_rightMul_prod Γ).comp (continuous_snd.prodMk continuous_fst)`. Establish `hmeas : StronglyMeasurable (uncurry fun (g : G) (x : RightCosetSpace Γ) => f g * φ (rightMul Γ g x))` using `(f.continuous.comp continuous_fst).stronglyMeasurable.mul ((Lp.stronglyMeasurable φ).comp_measurable hcont.measurable)`. Use `⟨hmeas.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `hφ1 : ∫⁻ x, ‖φ x‖ₑ ∂quotientMeasure Γ μ < ⊤` using `((Lp.memLp φ).integrable one_le_two).2`. Establish `hf1 : ∫⁻ g, ‖f g‖ₑ ∂μ < ⊤` using `(f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).2`.

Rewrite using `[hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.aestronglyMeasurable.enorm]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `g`. Simplify using `only [uncurry_apply_pair, enorm_mul]`.

Rewrite using `[lintegral_const_mul' _ _ enorm_ne_top, (measurePreserving_rightMul μ g).lintegral_comp (Lp.stronglyMeasurable φ).measurable.enorm]`. Use `_ = (∫⁻ g, ‖f g‖ₑ ∂μ) * ∫⁻ x, ‖φ x‖ₑ ∂quotientMeasure Γ μ := lintegral_mul_const' _ _ hφ1.ne`. Use `_ < ⊤ := ENNReal.mul_lt_top hf1 hφ1`.
-/
theorem integrable_prod_rightMul (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    Integrable (uncurry fun (g : G) (x : RightCosetSpace Γ) => f g * φ (rightMul Γ g x))
      (μ.prod (quotientMeasure Γ μ)) := by
  have hcont : Continuous fun p : G × RightCosetSpace Γ => rightMul Γ p.1 p.2 :=
    (continuous_rightMul_prod Γ).comp (continuous_snd.prodMk continuous_fst)
  have hmeas : StronglyMeasurable
      (uncurry fun (g : G) (x : RightCosetSpace Γ) => f g * φ (rightMul Γ g x)) :=
    (f.continuous.comp continuous_fst).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable φ).comp_measurable hcont.measurable)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hφ1 : ∫⁻ x, ‖φ x‖ₑ ∂quotientMeasure Γ μ < ⊤ := ((Lp.memLp φ).integrable one_le_two).2
  have hf1 : ∫⁻ g, ‖f g‖ₑ ∂μ < ⊤ :=
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).2
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.aestronglyMeasurable.enorm]
  calc ∫⁻ g, ∫⁻ x, ‖uncurry (fun g x => f g * φ (rightMul Γ g x)) (g, x)‖ₑ ∂quotientMeasure Γ μ ∂μ
      = ∫⁻ g, ‖f g‖ₑ * ∫⁻ x, ‖φ x‖ₑ ∂quotientMeasure Γ μ ∂μ := by
        congr 1
        ext g
        simp only [uncurry_apply_pair, enorm_mul]
        rw [lintegral_const_mul' _ _ enorm_ne_top,
          (measurePreserving_rightMul μ g).lintegral_comp (Lp.stronglyMeasurable φ).measurable.enorm]
    _ = (∫⁻ g, ‖f g‖ₑ ∂μ) * ∫⁻ x, ‖φ x‖ₑ ∂quotientMeasure Γ μ := lintegral_mul_const' _ _ hφ1.ne
    _ < ⊤ := ENNReal.mul_lt_top hf1 hφ1

/- English proof (translation)
Take `⟨a, rfl⟩` from `mk_surjective Γ x`. Rewrite using `[rconvQ_mk, rconv, ← integral_mul_left_eq_self _ a]`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[inv_mul_cancel_left, rightMul_mk]`.
-/
theorem rconvQ_eq_integral (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (x : RightCosetSpace Γ) :
    rconvQ Γ μ f φ x = ∫ g, f g * φ (rightMul Γ g x) ∂μ := by
  obtain ⟨a, rfl⟩ := mk_surjective Γ x
  rw [rconvQ_mk, rconv, ← integral_mul_left_eq_self _ a]
  congr 1
  ext g
  rw [inv_mul_cancel_left, rightMul_mk]

/- English proof (translation)
Use `(integrable_prod_rightMul Γ μ f φ).integral_prod_right` as an intermediate fact. Use `this.congr (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [uncurry_apply_pair]`. Conclude with `(rconvQ_eq_integral Γ μ f φ x).symm`.
-/
theorem integrable_rconvQ (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) : Integrable (rconvQ Γ μ f φ) (quotientMeasure Γ μ) := by
  have := (integrable_prod_rightMul Γ μ f φ).integral_prod_right
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [uncurry_apply_pair]
  exact (rconvQ_eq_integral Γ μ f φ x).symm

/- English proof (translation)
Establish `hint` using `integrable_rconvQ Γ μ f φ`. Use `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn) (fun s _ _ => hint.integrableOn) fun s hs hμs => ?_` and prove the remaining obligations. Rewrite using `[← L2.inner_indicatorConstLp_one hs hμs.ne, UnitaryRep.inner_integrated]`. Establish `hcoef : ∀ g, ⟪indicatorConstLp 2 hs hμs.ne (1 : ℂ), rightRegularRep Γ μ g φ⟫_ℂ = ∫ x in s, φ (rightMul Γ g x) ∂quotientMeasure Γ μ`. Introduce `g`.

Rewrite using `[L2.inner_indicatorConstLp_one]`. Conclude with `setIntegral_congr_ae hs ((coeFn_rightRegularRep Γ μ g φ).mono fun x hx _ => hx)`. Establish `hFs : Integrable (uncurry fun (g : G) (x : RightCosetSpace Γ) => f g * φ (rightMul Γ g x)) (μ.prod ((quotientMeasure Γ μ).restrict s))`. Use `(integrable_prod_rightMul Γ μ f φ).restrict (s := univ ×ˢ s)` as an intermediate fact. Rewrite `this` using `[← Measure.prod_restrict, Measure.restrict_univ]`. Then use the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae ((coeFn_compactSupportToL1 μ f).mono fun g hg => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hg, hcoef, integral_const_mul]`. Use `_ = ∫ x in s, ∫ g, f g * φ (rightMul Γ g x) ∂μ ∂quotientMeasure Γ μ := integral_integral_swap hFs`.

Use `_ = ∫ x in s, rconvQ Γ μ f φ x ∂quotientMeasure Γ μ := by simp_rw [rconvQ_eq_integral]`.
-/
theorem integrated_ae_eq_rconvQ (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) :
    ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ : RightCosetSpace Γ → ℂ)
      =ᵐ[quotientMeasure Γ μ] rconvQ Γ μ f φ := by
  have hint := integrable_rconvQ Γ μ f φ
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn)
    (fun s _ _ => hint.integrableOn) fun s hs hμs => ?_
  rw [← L2.inner_indicatorConstLp_one hs hμs.ne, UnitaryRep.inner_integrated]
  have hcoef : ∀ g, ⟪indicatorConstLp 2 hs hμs.ne (1 : ℂ), rightRegularRep Γ μ g φ⟫_ℂ =
      ∫ x in s, φ (rightMul Γ g x) ∂quotientMeasure Γ μ := by
    intro g
    rw [L2.inner_indicatorConstLp_one]
    exact setIntegral_congr_ae hs ((coeFn_rightRegularRep Γ μ g φ).mono fun x hx _ => hx)
  have hFs : Integrable (uncurry fun (g : G) (x : RightCosetSpace Γ) => f g * φ (rightMul Γ g x))
      (μ.prod ((quotientMeasure Γ μ).restrict s)) := by
    have := (integrable_prod_rightMul Γ μ f φ).restrict (s := univ ×ˢ s)
    rwa [← Measure.prod_restrict, Measure.restrict_univ] at this
  calc ∫ g, (UnitaryRep.ccToL1 μ f) g *
        ⟪indicatorConstLp 2 hs hμs.ne 1, rightRegularRep Γ μ g φ⟫_ℂ ∂μ
      = ∫ g, ∫ x in s, f g * φ (rightMul Γ g x) ∂quotientMeasure Γ μ ∂μ := by
        refine integral_congr_ae ((coeFn_compactSupportToL1 μ f).mono fun g hg => ?_)
        dsimp only
        rw [hg, hcoef, integral_const_mul]
    _ = ∫ x in s, ∫ g, f g * φ (rightMul Γ g x) ∂μ ∂quotientMeasure Γ μ := integral_integral_swap hFs
    _ = ∫ x in s, rconvQ Γ μ f φ x ∂quotientMeasure Γ μ := by simp_rw [rconvQ_eq_integral]

end Operator

end RightCosetSpace

end

end GroundTheory.Automorphic
