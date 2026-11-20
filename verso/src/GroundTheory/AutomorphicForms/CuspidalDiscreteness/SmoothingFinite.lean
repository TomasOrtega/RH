import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

instance compactSpace_integralFiniteGL : CompactSpace (AdelicGLn.integralFiniteGL K n) :=
  isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL K n)

/- English proof (translation)
Set `` to `IsTopologicalGroup.rightUniformSpace (normOneGL K n)`. Establish `hu : UniformContinuous (g : normOneGL K n → ℂ)` using `g.hasCompactSupport.uniformContinuous_of_continuous g.continuous`. Establish `h` using `hu (Metric.dist_mem_uniformity hε)`. Rewrite `h` using `[uniformity_eq_comap_nhds_one']`. Take `⟨V, hV, hVsub⟩` from `Filter.mem_comap.1 h`.

Use `⟨V, hV, fun a ha x => ?_⟩` and prove the remaining obligations. Establish `hmem : ((a⁻¹ * x, x) : normOneGL K n × normOneGL K n) ∈ (fun p : normOneGL K n × normOneGL K n => p.2 * p.1⁻¹) ⁻¹' V`. Express the relevant statement in the definitionally equal form `x * (a⁻¹ * x)⁻¹ ∈ V`. Rewrite using `[mul_inv_rev, inv_inv, mul_inv_cancel_left]` and apply the resulting hypothesis. Use `hVsub hmem` as an intermediate fact.

Rewrite using `[← dist_eq_norm]`. Conclude with `(show dist (g (a⁻¹ * x)) (g x) < ε from this).le`.
-/
theorem exists_forall_norm_sub_le (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ V ∈ 𝓝 (1 : normOneGL K n), ∀ a ∈ V, ∀ x, ‖g (a⁻¹ * x) - g x‖ ≤ ε := by
  let := IsTopologicalGroup.rightUniformSpace (normOneGL K n)
  have hu : UniformContinuous (g : normOneGL K n → ℂ) :=
    g.hasCompactSupport.uniformContinuous_of_continuous g.continuous
  have h := hu (Metric.dist_mem_uniformity hε)
  rw [uniformity_eq_comap_nhds_one'] at h
  obtain ⟨V, hV, hVsub⟩ := Filter.mem_comap.1 h
  refine ⟨V, hV, fun a ha x => ?_⟩
  have hmem : ((a⁻¹ * x, x) : normOneGL K n × normOneGL K n) ∈
      (fun p : normOneGL K n × normOneGL K n => p.2 * p.1⁻¹) ⁻¹' V := by
    change x * (a⁻¹ * x)⁻¹ ∈ V
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have := hVsub hmem
  rw [← dist_eq_norm]
  exact (show dist (g (a⁻¹ * x)) (g x) < ε from this).le

section FinAvg

variable (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))

include hU in
/- English proof (translation)
The claim follows from `isCompact_iff_compactSpace.1 (U.isClosed_of_isOpen hU).isCompact`.
-/
theorem compactSpace_of_isOpen : CompactSpace U :=
  isCompact_iff_compactSpace.1 (U.isClosed_of_isOpen hU).isCompact

def haarProb (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] : Measure H :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)

section Prob

variable (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

instance : (haarProb H).IsHaarMeasure := by
  unfold haarProb
  infer_instance

instance : IsProbabilityMeasure (haarProb H) := by
  constructor
  rw [← TopologicalSpace.PositiveCompacts.coe_top (α := H)]
  exact Measure.haarMeasure_self

end Prob

def finAvgFun (g : normOneGL K n → ℂ) (x : normOneGL K n) : ℂ :=
  have := compactSpace_of_isOpen U hU
  ∫ u : U, g ((finOne K n u)⁻¹ * x) ∂haarProb U

/- English proof (translation)
Use `compactSpace_of_isOpen U hU` as an intermediate fact. Establish `: finAvgFun U hU g = fun x => ∫ u in (univ : Set U), g ((finOne K n u)⁻¹ * x) ∂haarProb U`. Use function extensionality and compare the values at `x`. Rewrite using `[Measure.restrict_univ]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Use `continuous_parametric_integral_of_continuous ?_ isCompact_univ` and prove the remaining obligations. Conclude with `g.continuous.comp (((continuous_finOne.comp (continuous_subtype_val.comp continuous_snd)).inv).mul continuous_fst)`.
-/
theorem continuous_finAvgFun (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    Continuous (finAvgFun U hU g) := by
  have := compactSpace_of_isOpen U hU
  have : finAvgFun U hU g = fun x => ∫ u in (univ : Set U), g ((finOne K n u)⁻¹ * x) ∂haarProb U := by
    funext x
    rw [Measure.restrict_univ]
    rfl
  rw [this]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_univ
  exact g.continuous.comp (((continuous_finOne.comp (continuous_subtype_val.comp
    continuous_snd)).inv).mul continuous_fst)

/- English proof (translation)
Use `compactSpace_of_isOpen U hU` as an intermediate fact. Use `integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `: (finOne K n u)⁻¹ * x ∉ tsupport (g : normOneGL K n → ℂ)` using `fun h => hx ⟨finOne K n u, ⟨u, mem_univ _, rfl⟩, _, h, mul_inv_cancel_left _ _⟩`. Conclude with `image_eq_zero_of_notMem_tsupport this`.
-/
theorem finAvgFun_eq_zero_of_notMem (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {x : normOneGL K n}
    (hx : x ∉ (fun u : U => finOne K n u) '' univ * tsupport (g : normOneGL K n → ℂ)) :
    finAvgFun U hU g x = 0 := by
  have := compactSpace_of_isOpen U hU
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  have : (finOne K n u)⁻¹ * x ∉ tsupport (g : normOneGL K n → ℂ) := fun h =>
    hx ⟨finOne K n u, ⟨u, mem_univ _, rfl⟩, _, h, mul_inv_cancel_left _ _⟩
  exact image_eq_zero_of_notMem_tsupport this

include hU in
/- English proof (translation)
The claim follows from `have := compactSpace_of_isOpen U hU isCompact_univ.image (continuous_finOne.comp continuous_subtype_val)`.
-/
theorem isCompact_finOne_image : IsCompact ((fun u : U => finOne K n (u : AdelicGLn.integralFiniteGL K n)) '' univ) :=
  have := compactSpace_of_isOpen U hU
  isCompact_univ.image (continuous_finOne.comp continuous_subtype_val)

def finAvg (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    CompactlySupportedContinuousMap (normOneGL K n) ℂ :=
  ⟨⟨finAvgFun U hU g, continuous_finAvgFun U hU g⟩,
    HasCompactSupport.intro ((isCompact_finOne_image U hU).mul g.hasCompactSupport)
      fun _ hx => finAvgFun_eq_zero_of_notMem U hU g hx⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem finAvg_apply (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (x : normOneGL K n) : finAvg U hU g x = finAvgFun U hU g x := rfl

/- English proof (translation)
Use `compactSpace_of_isOpen U hU` as an intermediate fact. Unfold `finAvgFun`. Rewrite using `[← integral_mul_left_eq_self (fun u : U => g ((finOne K n u)⁻¹ * (finOne K n v * x))) v]`. Use `integral_congr_ae (Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g ((finOne K n ((v * u : U) : AdelicGLn.integralFiniteGL K n))⁻¹ * (finOne K n v * x)) = _`.

Rewrite using `[Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]`.
-/
theorem finAvgFun_finOne_mul (g : normOneGL K n → ℂ) (v : U) (x : normOneGL K n) :
    finAvgFun U hU g (finOne K n v * x) = finAvgFun U hU g x := by
  have := compactSpace_of_isOpen U hU
  unfold finAvgFun
  rw [← integral_mul_left_eq_self (fun u : U => g ((finOne K n u)⁻¹ * (finOne K n v * x))) v]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  change g ((finOne K n ((v * u : U) : AdelicGLn.integralFiniteGL K n))⁻¹ * (finOne K n v * x)) = _
  rw [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/- English proof (translation)
Use `compactSpace_of_isOpen U hU` as an intermediate fact. Establish `hi1 : Integrable (fun u : U => g ((finOne K n u)⁻¹ * x)) (haarProb U)` using `(g.continuous.comp (((continuous_finOne.comp continuous_subtype_val).inv).mul continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hgx : g x = ∫ _u : U, g x ∂haarProb U` using `by simp`. Rewrite using `[hgx, finAvgFun, ← integral_sub hi1 (integrable_const _)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_finAvgFun_sub_le (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {ε : ℝ}
    (hg : ∀ u : U, ∀ x, ‖g ((finOne K n u)⁻¹ * x) - g x‖ ≤ ε) (x : normOneGL K n) :
    ‖finAvgFun U hU g x - g x‖ ≤ ε := by
  have := compactSpace_of_isOpen U hU
  have hi1 : Integrable (fun u : U => g ((finOne K n u)⁻¹ * x)) (haarProb U) :=
    (g.continuous.comp (((continuous_finOne.comp continuous_subtype_val).inv).mul
      continuous_const)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgx : g x = ∫ _u : U, g x ∂haarProb U := by simp
  rw [hgx, finAvgFun, ← integral_sub hi1 (integrable_const _)]
  calc ‖∫ u : U, (g ((finOne K n u)⁻¹ * x) - g x) ∂haarProb U‖
      ≤ ∫ _u : U, ε ∂haarProb U :=
        norm_integral_le_of_norm_le (integrable_const _) (Eventually.of_forall fun u => hg u x)
    _ = ε := by simp

end FinAvg

/- English proof (translation)
Take `⟨V₀, hV₀c, hV₀⟩` from `exists_compact_mem_nhds (1 : normOneGL K n)`. Use `set Wc := V₀ * (V₀ * tsupport (g : normOneGL K n → ℂ))`. Establish `hWc : IsCompact Wc` using `hV₀c.mul (hV₀c.mul g.hasCompactSupport)`. Use `set M := μ.real Wc`. Establish `hM : 0 ≤ M` using `measureReal_nonneg`.

Use `set ε₁ := ε / (2 * M + 2)`. Establish `hε₁ : 0 < ε₁` using `div_pos hε (by positivity)`. Take `⟨V₁, hV₁, hgV₁⟩` from `exists_forall_norm_sub_le g hε₁`. Use `set V := V₁ ∩ V₀`. Establish `hV : V ∈ 𝓝 (1 : normOneGL K n)` using `inter_mem hV₁ hV₀`.

Establish `hUo : IsOpen ((finOne K n) ⁻¹' interior V)` using `isOpen_interior.preimage continuous_finOne`. Establish `hU1 : (1 : AdelicGLn.integralFiniteGL K n) ∈ (finOne K n) ⁻¹' interior V`. Rewrite using `[mem_preimage, map_one]`. Conclude with `mem_interior_iff_mem_nhds.2 hV`. Take `⟨H, hH⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1`.

Use `set U : Subgroup (AdelicGLn.integralFiniteGL K n) := H.toOpenSubgroup.toSubgroup`. Establish `hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))` using `H.toOpenSubgroup.isOpen`. Establish `hUV : ∀ u : U, finOne K n u ∈ V` using `fun u => interior_subset (hH u.2)`. Use `set W : Set (ArchUnits K n) := (archProj K n) ⁻¹' interior V`. Establish `hW : W ∈ 𝓝 (1 : ArchUnits K n)`.

Use `(isOpen_interior.preimage continuous_archProj).mem_nhds ?_` and prove the remaining obligations. Rewrite using `[mem_preimage, map_one]`. Conclude with `mem_interior_iff_mem_nhds.2 hV`. Establish `hWE : (Units.val : ArchUnits K n → ArchMatrix K n) '' W ∈ 𝓝 (1 : ArchMatrix K n)` using `Units.isOpenMap_val.image_mem_nhds hW`. Take `⟨b, hbsupp, hbc, hbsmooth, hbrange, hb1⟩` from `exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hWE`.

Establish `hb0 : ∀ A, 0 ≤ b A` using `fun A => (hbrange ⟨A, rfl⟩).1`. Establish `hbu : tsupport b ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)` using `hbsupp.trans (image_subset_range _ _)`. Use `set c := ∫ A : ArchUnits K n, b A ∂ν`. Establish `hc : 0 < c`. Use `(hbsmooth.continuous.comp Units.continuous_val).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) ?_ (fun A => hb0 _) (by simp [hb1])` and prove the remaining obligations.

Conclude with `HasCompactSupport.intro (isCompact_unitsSupport hbc hbu) fun A hA => image_eq_zero_of_notMem_tsupport (f := b) hA`. Use `set β : ArchMatrix K n → ℝ := fun A => b A * c⁻¹`. Establish `hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β` using `hbsmooth.mul contDiff_const`. Establish `hβc : HasCompactSupport β` using `hbc.mul_right`. Establish `hβsupp : tsupport β ⊆ tsupport b` using `tsupport_mul_subset_left`.

Establish `hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)` using `hβsupp.trans hbu`. Establish `hβ0 : ∀ A, 0 ≤ β A` using `fun A => mul_nonneg (hb0 A) (inv_nonneg.2 hc.le)`. Establish `hβ1 : ∫ A : ArchUnits K n, β A ∂ν = 1`. Simplify using `only [β]`. Rewrite using `[integral_mul_const, mul_inv_cancel₀ hc.ne']`.

Establish `hβV : ∀ A : ArchUnits K n, (A : ArchMatrix K n) ∈ tsupport β → archProj K n A ∈ V`. Introduce `A hA`. Take `⟨A', hA', hAA'⟩` from `hbsupp (hβsupp hA)`. Rewrite `hA'` using `[Units.ext hAA']`. Conclude with `interior_subset hA'`.

Use `⟨U, hU, β, hβ, hβc, hβu, hβ0, ?_⟩` and prove the remaining obligations. Use `set h := finAvg U hU g`. Establish `hhg : ∀ y, ‖h y - g y‖ ≤ ε₁` using `fun y => norm_finAvgFun_sub_le U hU g (fun u x => hgV₁ _ (hUV u).1 x) y`. Establish `hpt : ∀ x, ‖archConv ν hβ.continuous hβc hβu h x - g x‖ ≤ 2 * ε₁`. Introduce `x`.

Establish `h1` using `norm_archConvFun_sub_archConvFun_le ν hβ.continuous hβc hβu hβ0 hβ1 g h hhg x`. Establish `h2` using `norm_archConvFun_sub_le ν hβ.continuous hβc hβu hβ0 hβ1 hβV g (fun a ha x => hgV₁ a ha.1 x) x`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[archConv_apply]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ε₁ + ε₁ := (norm_add_le _ _).trans (add_le_add h1 h2)`. Use `_ = 2 * ε₁ := by ring`. Establish `hzero : ∀ x ∉ Wc, ‖archConv ν hβ.continuous hβc hβu h x - g x‖ = 0`. Introduce `x hx`.

Establish `hg0 : g x = 0`. Use `image_eq_zero_of_notMem_tsupport fun hxg => hx ?_` and prove the remaining obligations. Conclude with `⟨1, mem_of_mem_nhds hV₀, x, ⟨1, mem_of_mem_nhds hV₀, x, hxg, one_mul x⟩, one_mul x⟩`. Establish `htsupp : tsupport (h : normOneGL K n → ℂ) ⊆ (fun u : U => finOne K n (u : AdelicGLn.integralFiniteGL K n)) '' univ * tsupport (g : normOneGL K n → ℂ)`. Use `closure_minimal (fun y hy => ?_) ((isCompact_finOne_image U hU).mul g.hasCompactSupport).isClosed` and prove the remaining obligations.

Assume the negation of the conclusion as `hyC`. Conclude with `hy (finAvgFun_eq_zero_of_notMem U hU g hyC)`. Establish `hf0 : archConvFun ν β h x = 0`. Use `archConvFun_eq_zero_of_notMem ν h fun hxs => hx ?_` and prove the remaining obligations. Take `⟨a, ⟨A, hA, rfl⟩, y, hy, rfl⟩` from `hxs`.

Take `⟨_, ⟨u, -, rfl⟩, z, hz, rfl⟩` from `htsupp hy`. Conclude with `⟨archProj K n A, (hβV A hA).2, finOne K n u * z, ⟨finOne K n u, (hUV u).2, z, hz, rfl⟩, rfl⟩`. Rewrite using `[archConv_apply, hf0, hg0, sub_zero, norm_zero]`. Combine the equalities or inequalities in the displayed calculation. Use `(Real.le_norm_self _).trans ?_` and prove the remaining obligations.

Use `norm_setIntegral_le_of_norm_le_const hWc.measure_lt_top fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (norm_nonneg _)]`. Conclude with `hpt x`. Use `_ ≤ ε := by`. Simplify using `only [ε₁]`.

Rewrite using `[mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_smooth_approx (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure]
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
      (β : ArchMatrix K n → ℝ) (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
      (hβc : HasCompactSupport β)
      (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)),
      (∀ A, 0 ≤ β A) ∧
      ∫ x, ‖archConv ν hβ.continuous hβc hβu (finAvg U hU g) x - g x‖ ∂μ ≤ ε := by
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : normOneGL K n)
  set Wc := V₀ * (V₀ * tsupport (g : normOneGL K n → ℂ))
  have hWc : IsCompact Wc := hV₀c.mul (hV₀c.mul g.hasCompactSupport)
  set M := μ.real Wc
  have hM : 0 ≤ M := measureReal_nonneg
  set ε₁ := ε / (2 * M + 2)
  have hε₁ : 0 < ε₁ := div_pos hε (by positivity)
  obtain ⟨V₁, hV₁, hgV₁⟩ := exists_forall_norm_sub_le g hε₁
  set V := V₁ ∩ V₀
  have hV : V ∈ 𝓝 (1 : normOneGL K n) := inter_mem hV₁ hV₀

  have hUo : IsOpen ((finOne K n) ⁻¹' interior V) := isOpen_interior.preimage continuous_finOne
  have hU1 : (1 : AdelicGLn.integralFiniteGL K n) ∈ (finOne K n) ⁻¹' interior V := by
    rw [mem_preimage, map_one]
    exact mem_interior_iff_mem_nhds.2 hV
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  set U : Subgroup (AdelicGLn.integralFiniteGL K n) := H.toOpenSubgroup.toSubgroup
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) := H.toOpenSubgroup.isOpen
  have hUV : ∀ u : U, finOne K n u ∈ V := fun u => interior_subset (hH u.2)

  set W : Set (ArchUnits K n) := (archProj K n) ⁻¹' interior V
  have hW : W ∈ 𝓝 (1 : ArchUnits K n) := by
    refine (isOpen_interior.preimage continuous_archProj).mem_nhds ?_
    rw [mem_preimage, map_one]
    exact mem_interior_iff_mem_nhds.2 hV
  have hWE : (Units.val : ArchUnits K n → ArchMatrix K n) '' W ∈ 𝓝 (1 : ArchMatrix K n) :=
    Units.isOpenMap_val.image_mem_nhds hW
  obtain ⟨b, hbsupp, hbc, hbsmooth, hbrange, hb1⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hWE
  have hb0 : ∀ A, 0 ≤ b A := fun A => (hbrange ⟨A, rfl⟩).1
  have hbu : tsupport b ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) :=
    hbsupp.trans (image_subset_range _ _)
  set c := ∫ A : ArchUnits K n, b A ∂ν
  have hc : 0 < c := by
    refine (hbsmooth.continuous.comp Units.continuous_val).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := 1) ?_ (fun A => hb0 _) (by simp [hb1])
    exact HasCompactSupport.intro (isCompact_unitsSupport hbc hbu) fun A hA =>
      image_eq_zero_of_notMem_tsupport (f := b) hA
  set β : ArchMatrix K n → ℝ := fun A => b A * c⁻¹
  have hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β := hbsmooth.mul contDiff_const
  have hβc : HasCompactSupport β := hbc.mul_right
  have hβsupp : tsupport β ⊆ tsupport b := tsupport_mul_subset_left
  have hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := hβsupp.trans hbu
  have hβ0 : ∀ A, 0 ≤ β A := fun A => mul_nonneg (hb0 A) (inv_nonneg.2 hc.le)
  have hβ1 : ∫ A : ArchUnits K n, β A ∂ν = 1 := by
    simp only [β]
    rw [integral_mul_const, mul_inv_cancel₀ hc.ne']
  have hβV : ∀ A : ArchUnits K n, (A : ArchMatrix K n) ∈ tsupport β → archProj K n A ∈ V := by
    intro A hA
    obtain ⟨A', hA', hAA'⟩ := hbsupp (hβsupp hA)
    rw [Units.ext hAA'] at hA'
    exact interior_subset hA'
  refine ⟨U, hU, β, hβ, hβc, hβu, hβ0, ?_⟩
  set h := finAvg U hU g
  have hhg : ∀ y, ‖h y - g y‖ ≤ ε₁ := fun y =>
    norm_finAvgFun_sub_le U hU g (fun u x => hgV₁ _ (hUV u).1 x) y
  have hpt : ∀ x, ‖archConv ν hβ.continuous hβc hβu h x - g x‖ ≤ 2 * ε₁ := by
    intro x
    have h1 := norm_archConvFun_sub_archConvFun_le ν hβ.continuous hβc hβu hβ0 hβ1 g h hhg x
    have h2 := norm_archConvFun_sub_le ν hβ.continuous hβc hβu hβ0 hβ1 hβV g
      (fun a ha x => hgV₁ a ha.1 x) x
    calc ‖archConv ν hβ.continuous hβc hβu h x - g x‖
        = ‖(archConvFun ν β h x - archConvFun ν β g x) + (archConvFun ν β g x - g x)‖ := by
          rw [archConv_apply]; congr 1; ring
      _ ≤ ε₁ + ε₁ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = 2 * ε₁ := by ring
  have hzero : ∀ x ∉ Wc, ‖archConv ν hβ.continuous hβc hβu h x - g x‖ = 0 := by
    intro x hx
    have hg0 : g x = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hxg => hx ?_
      exact ⟨1, mem_of_mem_nhds hV₀, x, ⟨1, mem_of_mem_nhds hV₀, x, hxg, one_mul x⟩, one_mul x⟩
    have htsupp : tsupport (h : normOneGL K n → ℂ) ⊆
        (fun u : U => finOne K n (u : AdelicGLn.integralFiniteGL K n)) '' univ *
          tsupport (g : normOneGL K n → ℂ) := by
      refine closure_minimal (fun y hy => ?_)
        ((isCompact_finOne_image U hU).mul g.hasCompactSupport).isClosed
      by_contra hyC
      exact hy (finAvgFun_eq_zero_of_notMem U hU g hyC)
    have hf0 : archConvFun ν β h x = 0 := by
      refine archConvFun_eq_zero_of_notMem ν h fun hxs => hx ?_
      obtain ⟨a, ⟨A, hA, rfl⟩, y, hy, rfl⟩ := hxs
      obtain ⟨_, ⟨u, -, rfl⟩, z, hz, rfl⟩ := htsupp hy
      exact ⟨archProj K n A, (hβV A hA).2, finOne K n u * z, ⟨finOne K n u, (hUV u).2, z, hz, rfl⟩,
        rfl⟩
    rw [archConv_apply, hf0, hg0, sub_zero, norm_zero]
  calc ∫ x, ‖archConv ν hβ.continuous hβc hβu h x - g x‖ ∂μ
      = ∫ x in Wc, ‖archConv ν hβ.continuous hβc hβu h x - g x‖ ∂μ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ 2 * ε₁ * M := by
        refine (Real.le_norm_self _).trans ?_
        refine norm_setIntegral_le_of_norm_le_const hWc.measure_lt_top fun x _ => ?_
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hpt x
    _ ≤ ε := by
        simp only [ε₁]
        rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

end CuspidalSpectrum

end

end GroundTheory.Automorphic
