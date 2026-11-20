import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ENNReal

namespace GlobalTheory.ConvGrowth

open GlobalTheory.AutomorphicL2Unitary

/- English proof (translation)
Establish `hm : AEStronglyMeasurable (lift Γ F) μ` using `aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)`. Rewrite using `[← lintegral_indicator hS, lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hS), ← lintegral_const_mul'' _ ((Lp.aestronglyMeasurable F).enorm.pow_const _)]`. Use `lintegral_mono fun q => ?_` and prove the remaining obligations. Establish `e : ∀ γ : Γ, S.indicator (fun z => ‖lift Γ F z‖ₑ ^ (2 : ℝ)) ((γ : G) * q.out) = {γ : Γ | (γ : G) * q.out ∈ S}.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) γ`. Introduce `γ`.

Distinguish the cases in `hγ : (γ : G) * q.out ∈ S`. Rewrite using `[Set.indicator_of_mem hγ, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]`. Simplify using `only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]`. Rewrite using `[Set.indicator_of_notMem hγ, Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]`. Rewrite using `[tsum_congr e, ← tsum_subtype, ENNReal.tsum_set_const]`.

Use `gcongr`. Conclude with `hN _`.
-/
theorem lintegral_sq_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℝ≥0∞) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : L2 Γ μ) :
    ∫⁻ z in S, ‖lift Γ F z‖ₑ ^ (2 : ℝ) ∂μ ≤ N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ := by
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  rw [← lintegral_indicator hS,
    lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hS),
    ← lintegral_const_mul'' _ ((Lp.aestronglyMeasurable F).enorm.pow_const _)]
  refine lintegral_mono fun q => ?_
  have e : ∀ γ : Γ, S.indicator (fun z => ‖lift Γ F z‖ₑ ^ (2 : ℝ)) ((γ : G) * q.out) =
      {γ : Γ | (γ : G) * q.out ∈ S}.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) γ := by
    intro γ
    by_cases hγ : (γ : G) * q.out ∈ S
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ,
        Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]
  rw [tsum_congr e, ← tsum_subtype, ENNReal.tsum_set_const]
  gcongr
  exact hN _

/- English proof (translation)
Introduce `D V μ _ _ Ω hΩ ⟨A, C, hC⟩`. Use `⟨A, (μ Ω ^ (1 / 2 : ℝ)).toReal * Real.sqrt (max C 0), ?_⟩` and prove the remaining obligations. Introduce `f' hf' hsupp M hM F g`. Use `set b : ℝ := Real.sqrt (max C 0) * GlobalTheory.Grow.height V g ^ A with hb`. Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM 1)`.

Establish `hh : 0 ≤ GlobalTheory.Grow.height V g` using `zero_le_one.trans (GlobalTheory.Grow.one_le_height V g)`. Establish `hb0 : 0 ≤ b` using `by positivity`. Use `set S : Set (GA D V) := (g * ·) '' Ω with hSdef`. Establish `hSc : IsCompact S` using `hΩ.image (continuous_const_mul g)`. Establish `hS : MeasurableSet S` using `hSc.isClosed.measurableSet`.

Establish `hcount : ∀ x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ S}.encard ≤ ENNReal.ofReal b ^ 2`. Introduce `x`. Take `⟨hfin, hle⟩` from `hC g x`. Rewrite using `[← hfin.cast_ncard_eq, ← ENNReal.ofReal_pow hb0]`. Establish `e : b ^ 2 = max C 0 * GlobalTheory.Grow.height V g ^ (2 * A)`.

Rewrite using `[hb, mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm A 2]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Use `set φ : GA D V → ℂ := GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F with hφ`. Establish `hm : AEStronglyMeasurable φ μ` using `aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)`.

Establish `hmp : MeasurePreserving (g * ·) (μ.restrict Ω) (μ.restrict S)`. Use `(measurePreserving_mul_left μ g).restrict_preimage_emb (measurableEmbedding_mulLeft g) S` as an intermediate fact. Rewrite `this` using `[hSdef, preimage_image_eq _ (mul_right_injective g)]`. Then use the resulting hypothesis. Establish `hm' : AEStronglyMeasurable (φ ∘ (g * ·)) (μ.restrict Ω)` using `hm.restrict.comp_measurePreserving hmp`. Establish `h1 : ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' φ g‖ₑ ≤ ENNReal.ofReal M * eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω)`.

Rewrite using `[eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hΩ.measurableSet]`. Use `(enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ Ω`. Rewrite using `[Set.indicator_of_mem hy, enorm_mul]`. Use `mul_le_mul_of_nonneg_right ?_ (zero_le)` and prove the remaining obligations.

Rewrite using `[← ofReal_norm]`. Conclude with `ENNReal.ofReal_le_ofReal (hM y)`. Rewrite using `[Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport fun h => hy (hsupp h)]`. Simplify using the standard rewrite rules. Establish `h2 : eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) ≤ eLpNorm φ 2 (μ.restrict S) * μ Ω ^ (1 / 2 : ℝ)`.

Use `(eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm').trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[eLpNorm_comp_measurePreserving hm.restrict hmp, Measure.restrict_apply_univ]`. Evaluate the numerical expressions. Establish `h3 : eLpNorm φ 2 (μ.restrict S) ≤ ENNReal.ofReal b * eLpNorm F 2 (quotMeasure (GQ V) μ)`. Rewrite using `[eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]`.

Simplify using `only [ENNReal.toReal_ofNat]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]`. Use `congr 1`. Rewrite using `[show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero]`.

Establish `hE` using `h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h3 zero_le)) zero_le)`. Establish `hμ : μ Ω ^ (1 / 2 : ℝ) ≠ ⊤` using `ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΩ.measure_lt_top.ne`. Establish `hfin : ENNReal.ofReal M * (ENNReal.ofReal b * eLpNorm F 2 (quotMeasure (GQ V) μ) * μ Ω ^ (1 / 2 : ℝ)) ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)) hμ)`. Use `ENNReal.toReal_mono hfin hE` as an intermediate fact. Rewrite `this` using `[toReal_enorm]`.

Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0, ENNReal.toReal_ofReal hb0, ← Lp.norm_def, hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_convR_le_height : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Ω : Set (GA D V)}, IsCompact Ω → (∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A)) → ∃ (A : ℕ) (C : ℝ), ∀ f' : GA D V → ℂ, Continuous f' → tsupport f' ⊆ Ω → ∀ M : ℝ, (∀ y, ‖f' y‖ ≤ M) → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (g : GA D V), ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g‖ ≤ C * M * ‖F‖ * GlobalTheory.Grow.height V g ^ A := by
  intro D V μ _ _ Ω hΩ ⟨A, C, hC⟩
  refine ⟨A, (μ Ω ^ (1 / 2 : ℝ)).toReal * Real.sqrt (max C 0), ?_⟩
  intro f' hf' hsupp M hM F g
  set b : ℝ := Real.sqrt (max C 0) * GlobalTheory.Grow.height V g ^ A with hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hh : 0 ≤ GlobalTheory.Grow.height V g := zero_le_one.trans (GlobalTheory.Grow.one_le_height V g)
  have hb0 : 0 ≤ b := by positivity
  set S : Set (GA D V) := (g * ·) '' Ω with hSdef
  have hSc : IsCompact S := hΩ.image (continuous_const_mul g)
  have hS : MeasurableSet S := hSc.isClosed.measurableSet
  have hcount : ∀ x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ S}.encard ≤ ENNReal.ofReal b ^ 2 := by
    intro x
    obtain ⟨hfin, hle⟩ := hC g x
    rw [← hfin.cast_ncard_eq, ← ENNReal.ofReal_pow hb0]
    have e : b ^ 2 = max C 0 * GlobalTheory.Grow.height V g ^ (2 * A) := by
      rw [hb, mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm A 2]
    rw [e]
    calc (((({γ : GQ V | (γ : GA D V) * x ∈ S}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞)
        = ENNReal.ofReal ({γ : GQ V | (γ : GA D V) * x ∈ S}.ncard : ℝ) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  set φ : GA D V → ℂ := GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F with hφ
  have hm : AEStronglyMeasurable φ μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have hmp : MeasurePreserving (g * ·) (μ.restrict Ω) (μ.restrict S) := by
    have := (measurePreserving_mul_left μ g).restrict_preimage_emb (measurableEmbedding_mulLeft g) S
    rwa [hSdef, preimage_image_eq _ (mul_right_injective g)] at this
  have hm' : AEStronglyMeasurable (φ ∘ (g * ·)) (μ.restrict Ω) :=
    hm.restrict.comp_measurePreserving hmp

  have h1 : ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' φ g‖ₑ ≤ ENNReal.ofReal M * eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator hΩ.measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy, enorm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (zero_le)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hM y)
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport fun h => hy (hsupp h)]
      simp

  have h2 : eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) ≤ eLpNorm φ 2 (μ.restrict S) * μ Ω ^ (1 / 2 : ℝ) := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm').trans (le_of_eq ?_)
    rw [eLpNorm_comp_measurePreserving hm.restrict hmp, Measure.restrict_apply_univ]
    norm_num

  have h3 : eLpNorm φ 2 (μ.restrict S) ≤ ENNReal.ofReal b * eLpNorm F 2 (quotMeasure (GQ V) μ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    calc (∫⁻ z in S, ‖φ z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal b ^ 2 * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure (GQ V) μ) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (lintegral_sq_le (GQ V) μ hS _ hcount F) (by norm_num)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero]
  have hE := h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h3 zero_le))
    zero_le)
  have hμ : μ Ω ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΩ.measure_lt_top.ne
  have hfin : ENNReal.ofReal M * (ENNReal.ofReal b * eLpNorm F 2 (quotMeasure (GQ V) μ) * μ Ω ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)) hμ)
  have := ENNReal.toReal_mono hfin hE
  rw [toReal_enorm] at this
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0,
    ENNReal.toReal_ofReal hb0, ← Lp.norm_def, hb]
  ring

end GlobalTheory.ConvGrowth
