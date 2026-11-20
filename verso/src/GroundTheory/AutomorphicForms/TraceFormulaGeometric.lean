import Mathlib
import GroundTheory.AutomorphicForms.KernelTrace
import GroundTheory.AutomorphicForms.TraceFormulaConvolution

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

section Algebra

variable {G : Type*} [Group G]

def centralizerIn (Γ : Subgroup G) (γ : G) : Subgroup G :=
  Γ ⊓ Subgroup.centralizer {γ}

/- English proof (translation)
The claim follows from `inf_le_right`.
-/
theorem centralizerIn_le_centralizer (Γ : Subgroup G) (γ : G) :
    centralizerIn Γ γ ≤ Subgroup.centralizer {γ} :=
  inf_le_right

/- English proof (translation)
The claim follows from `inf_le_left`.
-/
theorem centralizerIn_le (Γ : Subgroup G) (γ : G) : centralizerIn Γ γ ≤ Γ :=
  inf_le_left

/- English proof (translation)
Rewrite using `[Subgroup.mem_centralizer_iff]`. Simplify using `only [Set.mem_singleton_iff, forall_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[mul_assoc, h, inv_mul_cancel_left]`.

Introduce `h`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mem_centralizer_singleton_iff {γ δ : G} :
    δ ∈ Subgroup.centralizer {γ} ↔ δ⁻¹ * γ * δ = γ := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    rw [mul_assoc, h, inv_mul_cancel_left]
  · intro h
    calc γ * δ = δ * (δ⁻¹ * γ * δ) := by group
      _ = δ * γ := by rw [h]

/- English proof (translation)
Rewrite using `[centralizerIn, Subgroup.mem_inf, mem_centralizer_singleton_iff]`.
-/
theorem mem_centralizerIn {Γ : Subgroup G} {γ δ : G} :
    δ ∈ centralizerIn Γ γ ↔ δ ∈ Γ ∧ δ⁻¹ * γ * δ = γ := by
  rw [centralizerIn, Subgroup.mem_inf, mem_centralizer_singleton_iff]

def conjOrbitFun {E : Type*} (H : Subgroup G) {γ : G} (hH : H ≤ Subgroup.centralizer {γ})
    (f : G → E) : RightCosetSpace H → E :=
  Quotient.lift (fun x => f (x⁻¹ * γ * x)) (by
    rintro a b ⟨η, rfl⟩
    have h : (η : G)⁻¹ * γ * η = γ := mem_centralizer_singleton_iff.1 (hH η.2)
    change f (((η : G) * b)⁻¹ * γ * ((η : G) * b)) = f (b⁻¹ * γ * b)
    congr 1
    calc ((η : G) * b)⁻¹ * γ * ((η : G) * b) = b⁻¹ * ((η : G)⁻¹ * γ * η) * b := by group
      _ = b⁻¹ * γ * b := by rw [h])

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem conjOrbitFun_mk {E : Type*} (H : Subgroup G) {γ : G}
    (hH : H ≤ Subgroup.centralizer {γ}) (f : G → E) (x : G) :
    conjOrbitFun H hH f (mk H x) = f (x⁻¹ * γ * x) :=
  rfl

end Algebra

section Geometric

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

instance discreteTopology_centralizerIn (γ : G) : DiscreteTopology (centralizerIn Γ γ) :=
  DiscreteTopology.of_continuous_injective
    (f := Subgroup.inclusion (centralizerIn_le Γ γ))
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [μ.IsMulRightInvariant] in

/- English proof (translation)
Establish `h` using `(measurePreserving_mul_left μ a).setIntegral_preimage_emb (MeasurableEquiv.mulLeft a).measurableEmbedding F (a • s)`. Establish `hpre : (fun x => a * x) ⁻¹' (a • s) = s`. Use extensionality with `x`. Simplify using `[Set.mem_smul_set_iff_inv_smul_mem]`. Rewrite `h` using `[hpre]`.

Conclude with `h.symm`.
-/
theorem setIntegral_smul_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : G)
    (s : Set G) (F : G → E) : ∫ x in a • s, F x ∂μ = ∫ x in s, F (a * x) ∂μ := by
  have h := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding F (a • s)
  have hpre : (fun x => a * x) ⁻¹' (a • s) = s := by
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem]
  rw [hpre] at h
  exact h.symm

variable [CompactSpace (RightCosetSpace Γ)]

omit [μ.IsMulRightInvariant] in
/- English proof (translation)
Rewrite using `[← quotientMeasure_univ μ (isFundamentalDomain_fundamentalDomain Γ μ)]`. Conclude with `measure_lt_top _ _`.
-/
theorem measure_fundamentalDomain_lt_top : μ (fundamentalDomain Γ) < ∞ := by
  rw [← quotientMeasure_univ μ (isFundamentalDomain_fundamentalDomain Γ μ)]
  exact measure_lt_top _ _

/- English proof (translation)
Rewrite `hf`, the goal using `[integrated_rightRegularRep_eq_kernelOperator, kernelOperator_eq_contKernelOp]`. Conclude with `trace_contKernelOp _ _ hf`.
-/
theorem trace_integrated_eq_integral_diag (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) :
    trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)) =
      ∫ x, quotientKernel Γ f (x, x) ∂quotientMeasure Γ μ := by
  rw [integrated_rightRegularRep_eq_kernelOperator, kernelOperator_eq_contKernelOp] at hf ⊢
  exact trace_contKernelOp _ _ hf

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [CompactSpace (RightCosetSpace Γ)] in

/- English proof (translation)
Rewrite using `[integral_quotientMeasure]`. Use `setIntegral_congr_fun (measurableSet_fundamentalDomain Γ) fun x _ => ?_` and prove the remaining obligations. Rewrite using `[quotientKernel_mk, tsum_eq_finsum (finite_support_automorphicKernel Γ f (x, x))]`.
-/
theorem integral_diag_eq (f : CompactlySupportedContinuousMap G ℂ) :
    ∫ x, quotientKernel Γ f (x, x) ∂quotientMeasure Γ μ =
      ∫ x in fundamentalDomain Γ, ∑' γ : Γ, f (x⁻¹ * γ * x) ∂μ := by
  rw [integral_quotientMeasure]
  refine setIntegral_congr_fun (measurableSet_fundamentalDomain Γ) fun x _ => ?_
  rw [quotientKernel_mk, tsum_eq_finsum (finite_support_automorphicKernel Γ f (x, x))]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [CompactSpace (RightCosetSpace Γ)] in

/- English proof (translation)
Use `summable_of_hasFiniteSupport ((finite_support_automorphicKernel Γ f (x, x)).subset ?_)` and prove the remaining obligations. Introduce `γ hγ`. Simplify using `using hγ`.
-/
theorem summable_norm_conj (f : CompactlySupportedContinuousMap G ℂ) (x : G) :
    Summable fun γ : Γ => ‖f (x⁻¹ * γ * x)‖ := by
  refine summable_of_hasFiniteSupport ((finite_support_automorphicKernel Γ f (x, x)).subset ?_)
  intro γ hγ
  simpa using hγ

/- English proof (translation)
Set `fa : CompactlySupportedContinuousMap G ℂ` to `{ toFun := fun x => ((‖f x‖ : ℝ) : ℂ) continuous_toFun := Complex.continuous_ofReal.comp (continuous_norm.comp f.continuous) hasCompactSupport' := f.hasCompactSupport.norm.comp_left Complex.ofReal_zero }`. Use `⟨‖quotientKernelC Γ fa‖, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : ((∑' γ : Γ, ‖f (x⁻¹ * γ * x)‖ : ℝ) : ℂ) = quotientKernelC Γ fa (mk Γ x, mk Γ x)`. Rewrite using `[quotientKernelC_apply, quotientKernel_mk, ← tsum_eq_finsum (L := SummationFilter.unconditional Γ) (finite_support_automorphicKernel Γ fa (x, x))]`. Conclude with `Complex.ofReal_tsum (L := SummationFilter.unconditional Γ) (fun γ : Γ => ‖f (x⁻¹ * γ * x)‖)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun γ : Γ => norm_nonneg (f (x⁻¹ * γ * x)))]`. Use `_ ≤ ‖quotientKernelC Γ fa‖ := by`. Rewrite using `[h1]`. Conclude with `(quotientKernelC Γ fa).norm_coe_le_norm _`.
-/
theorem exists_bound_tsum_norm_conj (f : CompactlySupportedContinuousMap G ℂ) :
    ∃ M : ℝ, ∀ x : G, ∑' γ : Γ, ‖f (x⁻¹ * γ * x)‖ ≤ M := by
  let fa : CompactlySupportedContinuousMap G ℂ :=
    { toFun := fun x => ((‖f x‖ : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp (continuous_norm.comp f.continuous)
      hasCompactSupport' := f.hasCompactSupport.norm.comp_left Complex.ofReal_zero }
  refine ⟨‖quotientKernelC Γ fa‖, fun x => ?_⟩
  have h1 : ((∑' γ : Γ, ‖f (x⁻¹ * γ * x)‖ : ℝ) : ℂ) =
      quotientKernelC Γ fa (mk Γ x, mk Γ x) := by
    rw [quotientKernelC_apply, quotientKernel_mk,
      ← tsum_eq_finsum (L := SummationFilter.unconditional Γ) (finite_support_automorphicKernel Γ fa (x, x))]
    exact Complex.ofReal_tsum (L := SummationFilter.unconditional Γ) (fun γ : Γ => ‖f (x⁻¹ * γ * x)‖)
  calc ∑' γ : Γ, ‖f (x⁻¹ * γ * x)‖ = ‖((∑' γ : Γ, ‖f (x⁻¹ * γ * x)‖ : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun γ : Γ => norm_nonneg (f (x⁻¹ * γ * x)))]
    _ ≤ ‖quotientKernelC Γ fa‖ := by
        rw [h1]
        exact (quotientKernelC Γ fa).norm_coe_le_norm _

omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [μ.IsHaarMeasure]
  [μ.IsMulRightInvariant] [CompactSpace (RightCosetSpace Γ)] in

/- English proof (translation)
Take `⟨C, hC⟩` from `f.continuous.bounded_above_of_compact_support f.hasCompactSupport`. Use `Measure.integrableOn_of_bounded hs ?_ (ae_of_all _ fun x => hC _)` and prove the remaining obligations. Conclude with `(f.continuous.comp (by fun_prop)).aestronglyMeasurable`.
-/
theorem integrableOn_conj (f : CompactlySupportedContinuousMap G ℂ) (γ : G) {s : Set G}
    (hs : μ s ≠ ∞) : IntegrableOn (fun x => f (x⁻¹ * γ * x)) s μ := by
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  refine Measure.integrableOn_of_bounded hs ?_ (ae_of_all _ fun x => hC _)
  exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable

omit [μ.IsMulRightInvariant] in

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_bound_tsum_norm_conj Γ f`. Establish `hD` using `(measure_fundamentalDomain_lt_top Γ μ).ne`. Use `summable_of_sum_le (c := μ.real (fundamentalDomain Γ) * M) (fun γ => integral_nonneg fun _ => norm_nonneg _) fun S => ?_` and prove the remaining obligations. Rewrite using `[← integral_finsetSum S (fun γ _ => (integrableOn_conj μ f γ hD).norm)]`. Combine the equalities or inequalities in the displayed calculation.

Use `setIntegral_mono (integrable_finsetSum S fun γ _ => (integrableOn_conj μ f γ hD).norm) (integrableOn_const hD) fun x => ?_` and prove the remaining obligations. Conclude with `((summable_norm_conj Γ f x).sum_le_tsum S (fun _ _ => norm_nonneg _)).trans (hM x)`. Use `_ = μ.real (fundamentalDomain Γ) * M := by rw [setIntegral_const, smul_eq_mul]`.
-/
theorem summable_integral_norm_conj (f : CompactlySupportedContinuousMap G ℂ) :
    Summable fun γ : Γ => ∫ x in fundamentalDomain Γ, ‖f (x⁻¹ * γ * x)‖ ∂μ := by
  obtain ⟨M, hM⟩ := exists_bound_tsum_norm_conj Γ f
  have hD := (measure_fundamentalDomain_lt_top Γ μ).ne
  refine summable_of_sum_le (c := μ.real (fundamentalDomain Γ) * M)
    (fun γ => integral_nonneg fun _ => norm_nonneg _) fun S => ?_
  rw [← integral_finsetSum S (fun γ _ => (integrableOn_conj μ f γ hD).norm)]
  calc ∫ x in fundamentalDomain Γ, ∑ γ ∈ S, ‖f (x⁻¹ * γ * x)‖ ∂μ
      ≤ ∫ x in fundamentalDomain Γ, M ∂μ := by
        refine setIntegral_mono (integrable_finsetSum S fun γ _ => (integrableOn_conj μ f γ hD).norm)
          (integrableOn_const hD) fun x => ?_
        exact ((summable_norm_conj Γ f x).sum_le_tsum S (fun _ _ => norm_nonneg _)).trans (hM x)
    _ = μ.real (fundamentalDomain Γ) * M := by rw [setIntegral_const, smul_eq_mul]

/- English proof (translation)
Establish `hD` using `(measure_fundamentalDomain_lt_top Γ μ).ne`. Establish `hs` using `summable_integral_norm_conj Γ μ f`. Rewrite using `[trace_integrated_eq_integral_diag Γ μ f hf, integral_diag_eq, ← integral_tsum_of_summable_integral_norm (fun γ : Γ => integrableOn_conj μ f (γ : G) hD) hs]`. Conclude with `(hs.of_norm_bounded fun γ => norm_integral_le_integral_norm _).hasSum`.
-/
theorem hasSum_integral_conj (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) :
    HasSum (fun γ : Γ => ∫ x in fundamentalDomain Γ, f (x⁻¹ * γ * x) ∂μ)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) := by
  have hD := (measure_fundamentalDomain_lt_top Γ μ).ne
  have hs := summable_integral_norm_conj Γ μ f
  rw [trace_integrated_eq_integral_diag Γ μ f hf, integral_diag_eq,
    ← integral_tsum_of_summable_integral_norm (fun γ : Γ => integrableOn_conj μ f (γ : G) hD) hs]
  exact (hs.of_norm_bounded fun γ => norm_integral_le_integral_norm _).hasSum

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] in
/- English proof (translation)
Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]`.
-/
theorem mem_smul_set_iff' (a y : G) (s : Set G) : y ∈ a • s ↔ a⁻¹ * y ∈ s := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

omit [LocallyCompactSpace G] [T2Space G] [CompactSpace (RightCosetSpace Γ)] in
/- English proof (translation)
The claim follows from `(existsUnique_smul_mem_fundamentalDomain Γ y).unique h₁ h₂`.
-/
theorem eq_of_mul_mem_fundamentalDomain {η₁ η₂ : Γ} {y : G}
    (h₁ : (η₁ : G) * y ∈ fundamentalDomain Γ) (h₂ : (η₂ : G) * y ∈ fundamentalDomain Γ) :
    η₁ = η₂ :=
  (existsUnique_smul_mem_fundamentalDomain Γ y).unique h₁ h₂

omit [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [CompactSpace (RightCosetSpace Γ)]
  [μ.IsMulRightInvariant] in

/- English proof (translation)
Use `IsFundamentalDomain.mk' (MeasurableSet.iUnion fun i => (measurableSet_fundamentalDomain Γ).const_smul _).nullMeasurableSet fun x => ?_` and prove the remaining obligations. Take `⟨η, hη, -⟩` from `existsUnique_smul_mem_fundamentalDomain Γ x`. Express the relevant statement in the definitionally equal form `(η : G) * x ∈ fundamentalDomain Γ at hη`. Use `set i : {γ' : Γ // IsConj γ γ'} := ⟨η * γ * η⁻¹, isConj_iff.2 ⟨η, rfl⟩⟩ with hi_def`. Establish `hi : ((δ i : G))⁻¹ * γ * δ i = η * γ * (η : G)⁻¹`.

Use `congrArg Subtype.val (hδ i)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hmem : ((δ i : G) * η) ∈ centralizerIn Γ γ`.

Rewrite using `[mem_centralizerIn]`. Use `⟨Γ.mul_mem (δ i).2 η.2, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `⟨⟨_, hmem⟩, ?_, ?_⟩` and prove the remaining obligations. Use `mem_iUnion.2 ⟨i, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_smul_set_iff']`. Express the relevant statement in the definitionally equal form `((δ i : G))⁻¹ * (((δ i : G) * η) * x) ∈ _`. Use `hη using 1` and compare the differences between its conclusion and the goal. Use `group`. Introduce and unpack `⟨ε, hε⟩ hεx`.

Take `⟨j, hj⟩` from `mem_iUnion.1 hεx`. Rewrite `hj` using `[mem_smul_set_iff']`. Express the relevant statement in the definitionally equal form `((δ j : G))⁻¹ * (ε * x) ∈ _ at hj`. Establish `hεΓ : ε ∈ Γ` using `(mem_centralizerIn.1 hε).1`. Establish `hη' : (δ j)⁻¹ * (⟨ε, hεΓ⟩ : Γ) = η` using `eq_of_mul_mem_fundamentalDomain Γ (by push_cast; rw [mul_assoc]; exact hj) hη`.

Establish `hε' : ε = (δ j : G) * η`. Use `congrArg Subtype.val hη'` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[← this]`. Use `group`.

Establish `hc` using `(mem_centralizerIn.1 hε).2`. Rewrite `hc` using `[hε']`. Establish `hj1 : ((j.1 : Γ) : G) = (i.1 : G)`. Use `congrArg Subtype.val (hδ j)` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite using `[← this, hi_def]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Establish `hji : j = i` using `Subtype.ext (Subtype.ext hj1)`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `ε = (δ i : G) * η`. Rewrite using `[hε', hji]`.
-/
theorem isFundamentalDomain_iUnion_smul (γ : Γ) {δ : {γ' : Γ // IsConj γ γ'} → Γ}
    (hδ : ∀ i, (δ i)⁻¹ * γ * δ i = i.1) :
    IsFundamentalDomain (centralizerIn Γ γ)
      (⋃ i, ((δ i : Γ) : G) • fundamentalDomain Γ) μ := by
  refine IsFundamentalDomain.mk' (MeasurableSet.iUnion fun i =>
    (measurableSet_fundamentalDomain Γ).const_smul _).nullMeasurableSet fun x => ?_
  obtain ⟨η, hη, -⟩ := existsUnique_smul_mem_fundamentalDomain Γ x
  change (η : G) * x ∈ fundamentalDomain Γ at hη
  set i : {γ' : Γ // IsConj γ γ'} := ⟨η * γ * η⁻¹, isConj_iff.2 ⟨η, rfl⟩⟩ with hi_def
  have hi : ((δ i : G))⁻¹ * γ * δ i = η * γ * (η : G)⁻¹ := by
    have := congrArg Subtype.val (hδ i)
    push_cast at this
    rw [this]
    rfl
  have hmem : ((δ i : G) * η) ∈ centralizerIn Γ γ := by
    rw [mem_centralizerIn]
    refine ⟨Γ.mul_mem (δ i).2 η.2, ?_⟩
    calc ((δ i : G) * η)⁻¹ * γ * ((δ i : G) * η) = (η : G)⁻¹ * ((δ i : G)⁻¹ * γ * δ i) * η := by
          group
      _ = γ := by rw [hi]; group
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · refine mem_iUnion.2 ⟨i, ?_⟩
    rw [mem_smul_set_iff']
    change ((δ i : G))⁻¹ * (((δ i : G) * η) * x) ∈ _
    convert hη using 1
    group
  · rintro ⟨ε, hε⟩ hεx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hεx
    rw [mem_smul_set_iff'] at hj
    change ((δ j : G))⁻¹ * (ε * x) ∈ _ at hj
    have hεΓ : ε ∈ Γ := (mem_centralizerIn.1 hε).1
    have hη' : (δ j)⁻¹ * (⟨ε, hεΓ⟩ : Γ) = η :=
      eq_of_mul_mem_fundamentalDomain Γ (by push_cast; rw [mul_assoc]; exact hj) hη
    have hε' : ε = (δ j : G) * η := by
      have := congrArg Subtype.val hη'
      push_cast at this
      rw [← this]
      group
    have hc := (mem_centralizerIn.1 hε).2
    rw [hε'] at hc
    have hj1 : ((j.1 : Γ) : G) = (i.1 : G) := by
      have := congrArg Subtype.val (hδ j)
      push_cast at this
      rw [← this, hi_def]
      push_cast
      calc ((δ j : G))⁻¹ * γ * δ j
          = η * (((δ j : G) * η)⁻¹ * γ * ((δ j : G) * η)) * (η : G)⁻¹ := by group
        _ = η * γ * (η : G)⁻¹ := by rw [hc]
    have hji : j = i := Subtype.ext (Subtype.ext hj1)
    apply Subtype.ext
    change ε = (δ i : G) * η
    rw [hε', hji]

omit [μ.IsMulRightInvariant] in

/- English proof (translation)
Establish `hδ : ∀ i : {γ' : Γ // IsConj γ γ'}, ∃ d : Γ, d⁻¹ * γ * d = i.1` using `fun i => by`. Take `⟨c, hc⟩` from `isConj_iff.1 i.2`. Conclude with `⟨c⁻¹, by rw [inv_inv]; exact hc⟩`. Use `choose δ hδ using hδ`. Use `set E : {γ' : Γ // IsConj γ γ'} → Set G := fun i => ((δ i : Γ) : G) • fundamentalDomain Γ with hE`.

Establish `hD` using `(measure_fundamentalDomain_lt_top Γ μ).ne`. Establish `hEm : ∀ i, MeasurableSet (E i)` using `fun i => (measurableSet_fundamentalDomain Γ).const_smul _`. Establish `hEμ : ∀ i, μ (E i) ≠ ∞` using `fun i => by rw [hE]; dsimp only; rw [measure_smul]; exact hD`. Establish `hdisj : Pairwise (Disjoint on E)`. Introduce `i j hij`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `y hi hj`. Rewrite `hi`, `hj` using `[hE, mem_smul_set_iff']`. Establish `h` using `eq_of_mul_mem_fundamentalDomain Γ (η₁ := (δ i)⁻¹) (η₂ := (δ j)⁻¹) (by push_cast; exact hi) (by push_cast; exact hj)`. Apply `hij` to reduce the goal to its premises.

Rewrite `h` using `[inv_inj]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hδ i, ← hδ j, h]`. Establish `hconj : ∀ (i : {γ' : Γ // IsConj γ γ'}) (x : G), ((δ i : G) * x)⁻¹ * γ * ((δ i : G) * x) = x⁻¹ * (i.1 : G) * x`. Introduce `i x`.

Use `congrArg Subtype.val (hδ i)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[← this]`. Use `group`. Establish `hterm : ∀ i, ∫ x in E i, f (x⁻¹ * (γ : G) * x) ∂μ = ∫ x in fundamentalDomain Γ, f (x⁻¹ * (i.1 : G) * x) ∂μ`.

Introduce `i`. Rewrite using `[hE]`. Simplify using `only`. Rewrite using `[setIntegral_smul_set μ]`. Repeatedly rewrite using `[hconj]`.

Establish `hnorm : ∀ i, ∫ x in E i, ‖f (x⁻¹ * (γ : G) * x)‖ ∂μ = ∫ x in fundamentalDomain Γ, ‖f (x⁻¹ * (i.1 : G) * x)‖ ∂μ`. Introduce `i`. Rewrite using `[hE]`. Simplify using `only`. Rewrite using `[setIntegral_smul_set μ]`.

Repeatedly rewrite using `[hconj]`. Establish `hint : IntegrableOn (fun x => f (x⁻¹ * (γ : G) * x)) (⋃ i, E i) μ`. Use `integrableOn_iUnion_of_summable_integral_norm (fun i => integrableOn_conj μ f _ (hEμ i)) ?_` and prove the remaining obligations. Repeatedly rewrite using `[hnorm]`. Conclude with `(summable_integral_norm_conj Γ μ f).comp_injective Subtype.val_injective`.

Establish `h1` using `hasSum_integral_iUnion hEm hdisj hint`. Rewrite `h1` using `[hterm]`. Establish `hq : ∫ x, conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f x ∂quotientMeasure (centralizerIn Γ γ) μ = ∫ x in ⋃ i, E i, f (x⁻¹ * (γ : G) * x) ∂μ`. Rewrite using `[integral_quotientMeasure, IsFundamentalDomain.setIntegral_eq (isFundamentalDomain_fundamentalDomain _ μ) (isFundamentalDomain_iUnion_smul Γ μ γ hδ)]`. Both sides reduce to the same expression.

Introduce `g x`. Simplify using `only [mk_smul]`. Rewrite using `[hq]`. Conclude with `h1`.
-/
theorem hasSum_integral_conj_isConj (f : CompactlySupportedContinuousMap G ℂ) (γ : Γ) :
    HasSum (fun i : {γ' : Γ // IsConj γ γ'} =>
        ∫ x in fundamentalDomain Γ, f (x⁻¹ * (i.1 : G) * x) ∂μ)
      (∫ x, conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f x
        ∂quotientMeasure (centralizerIn Γ γ) μ) := by
  classical
  have hδ : ∀ i : {γ' : Γ // IsConj γ γ'}, ∃ d : Γ, d⁻¹ * γ * d = i.1 := fun i => by
    obtain ⟨c, hc⟩ := isConj_iff.1 i.2
    exact ⟨c⁻¹, by rw [inv_inv]; exact hc⟩
  choose δ hδ using hδ
  set E : {γ' : Γ // IsConj γ γ'} → Set G := fun i => ((δ i : Γ) : G) • fundamentalDomain Γ
    with hE
  have hD := (measure_fundamentalDomain_lt_top Γ μ).ne
  have hEm : ∀ i, MeasurableSet (E i) := fun i =>
    (measurableSet_fundamentalDomain Γ).const_smul _
  have hEμ : ∀ i, μ (E i) ≠ ∞ := fun i => by rw [hE]; dsimp only; rw [measure_smul]; exact hD
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro y hi hj
    rw [hE, mem_smul_set_iff'] at hi hj
    have h := eq_of_mul_mem_fundamentalDomain Γ (η₁ := (δ i)⁻¹) (η₂ := (δ j)⁻¹)
      (by push_cast; exact hi) (by push_cast; exact hj)
    apply hij
    rw [inv_inj] at h
    apply Subtype.ext
    rw [← hδ i, ← hδ j, h]
  have hconj : ∀ (i : {γ' : Γ // IsConj γ γ'}) (x : G),
      ((δ i : G) * x)⁻¹ * γ * ((δ i : G) * x) = x⁻¹ * (i.1 : G) * x := by
    intro i x
    have := congrArg Subtype.val (hδ i)
    push_cast at this
    rw [← this]
    group
  have hterm : ∀ i, ∫ x in E i, f (x⁻¹ * (γ : G) * x) ∂μ =
      ∫ x in fundamentalDomain Γ, f (x⁻¹ * (i.1 : G) * x) ∂μ := by
    intro i
    rw [hE]
    dsimp only
    rw [setIntegral_smul_set μ]
    simp_rw [hconj]
  have hnorm : ∀ i, ∫ x in E i, ‖f (x⁻¹ * (γ : G) * x)‖ ∂μ =
      ∫ x in fundamentalDomain Γ, ‖f (x⁻¹ * (i.1 : G) * x)‖ ∂μ := by
    intro i
    rw [hE]
    dsimp only
    rw [setIntegral_smul_set μ]
    simp_rw [hconj]
  have hint : IntegrableOn (fun x => f (x⁻¹ * (γ : G) * x)) (⋃ i, E i) μ := by
    refine integrableOn_iUnion_of_summable_integral_norm
      (fun i => integrableOn_conj μ f _ (hEμ i)) ?_
    simp_rw [hnorm]
    exact (summable_integral_norm_conj Γ μ f).comp_injective Subtype.val_injective
  have h1 := hasSum_integral_iUnion hEm hdisj hint
  simp_rw [hterm] at h1
  have hq : ∫ x, conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f x
        ∂quotientMeasure (centralizerIn Γ γ) μ = ∫ x in ⋃ i, E i, f (x⁻¹ * (γ : G) * x) ∂μ := by
    rw [integral_quotientMeasure, IsFundamentalDomain.setIntegral_eq
      (isFundamentalDomain_fundamentalDomain _ μ) (isFundamentalDomain_iUnion_smul Γ μ γ hδ)]
    · rfl
    · intro g x
      simp only [mk_smul]
  rw [hq]
  exact h1

def conjClassRep {α : Type*} [Monoid α] (c : ConjClasses α) : α :=
  (ConjClasses.exists_rep c).choose

/- English proof (translation)
The claim follows from `(ConjClasses.exists_rep c).choose_spec`.
-/
theorem mk_conjClassRep {α : Type*} [Monoid α] (c : ConjClasses α) :
    ConjClasses.mk (conjClassRep c) = c :=
  (ConjClasses.exists_rep c).choose_spec

/- English proof (translation)
Establish `h` using `hasSum_integral_conj Γ μ f hf`. Rewrite `h` using `[← (Equiv.sigmaFiberEquiv (ConjClasses.mk : Γ → ConjClasses Γ)).hasSum_iff]`. Use `h.sigma fun c => ?_` and prove the remaining obligations. Set `e : {γ' : Γ // IsConj (conjClassRep c) γ'} ≃ {γ' : Γ // ConjClasses.mk γ' = c}` to `Equiv.subtypeEquivRight fun γ' => by`. Establish `hc` using `mk_conjClassRep c`.

Prove the components needed by the constructor for the conclusion. Introduce `h'`. Rewrite using `[← hc]`. Conclude with `ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_comm.1 h')`. Introduce `h'`.

Rewrite `h'` using `[← hc]`. Conclude with `isConj_comm.1 (ConjClasses.mk_eq_mk_iff_isConj.1 h')`. Establish `h2` using `hasSum_integral_conj_isConj Γ μ f (conjClassRep c)`. Rewrite `h2` using `[← e.symm.hasSum_iff]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals rfl`.
-/
theorem hasSum_orbitalIntegral (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) :
    HasSum (fun c : ConjClasses Γ =>
        ∫ x, conjOrbitFun (centralizerIn Γ ((conjClassRep c : Γ) : G))
          (centralizerIn_le_centralizer Γ _) f x
          ∂quotientMeasure (centralizerIn Γ ((conjClassRep c : Γ) : G)) μ)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) := by
  have h := hasSum_integral_conj Γ μ f hf
  rw [← (Equiv.sigmaFiberEquiv (ConjClasses.mk : Γ → ConjClasses Γ)).hasSum_iff] at h
  refine h.sigma fun c => ?_
  let e : {γ' : Γ // IsConj (conjClassRep c) γ'} ≃ {γ' : Γ // ConjClasses.mk γ' = c} :=
    Equiv.subtypeEquivRight fun γ' => by
      have hc := mk_conjClassRep c
      constructor
      · intro h'
        rw [← hc]
        exact ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_comm.1 h')
      · intro h'
        rw [← hc] at h'
        exact isConj_comm.1 (ConjClasses.mk_eq_mk_iff_isConj.1 h')
  have h2 := hasSum_integral_conj_isConj Γ μ f (conjClassRep c)
  rw [← e.symm.hasSum_iff] at h2
  convert h2 using 1
  all_goals rfl

end Geometric

end RightCosetSpace

end

end GroundTheory.Automorphic
