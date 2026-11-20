import Mathlib

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

section Field

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace K`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := K)`. Use `letI : (Valued.v (R := K)).RankOne :=`. Use the proof step `{ hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Establish `: ProperSpace K` using `.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K`. Use `open scoped Valued in`. Conclude with `secondCountable_of_proper`.
-/
theorem secondCountable : SecondCountableTopology K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  open scoped Valued in
  exact secondCountable_of_proper

variable {K}

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨Units.mk0 γ hγ, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at hx hy ⊢`.

Establish `h` using `(valuation K).map_add (y - x) x`. Rewrite `h` using `[sub_add_cancel]`. Conclude with `h.trans (max_le hy.le hx)`.
-/
theorem isOpen_ball (γ : ValueGroupWithZero K) (hγ : γ ≠ 0) :
    IsOpen {x : K | valuation K x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation K).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hy.le hx)

/- English proof (translation)
The claim follows from `IsNonarchimedeanLocalField.isCompact_closedBall K γ`.
-/
theorem isCompact_ball (γ : ValueGroupWithZero K) : IsCompact {x : K | valuation K x ≤ γ} :=
  IsNonarchimedeanLocalField.isCompact_closedBall K γ

end Field

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : Set E :=
  {x | ∀ i, valuation K (b.repr x i) ≤ γ i}

/- English proof (translation)
Establish `h` using `IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap`. Conclude with `(continuous_apply i).comp h`.
-/
theorem continuous_coord (b : Basis ι K E) (i : ι) : Continuous fun x : E => b.repr x i := by
  have h := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
  exact (continuous_apply i).comp h

/- English proof (translation)
Use `haveI := IsModuleTopology.toContinuousAdd K E`. Conclude with `IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.symm.toLinearMap`.
-/
theorem continuous_equivFun_symm (b : Basis ι K E) : Continuous b.equivFun.symm := by
  haveI := IsModuleTopology.toContinuousAdd K E
  exact IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.symm.toLinearMap

/- English proof (translation)
Establish `e : box b γ = ⋂ i, (fun x : E => b.repr x i) ⁻¹' {a : K | valuation K a ≤ γ i}`. Use extensionality with `x`. Simplify using `[box]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun i => (isOpen_ball (γ i) (hγ i)).preimage (continuous_coord b i)`.
-/
theorem isOpen_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) :
    IsOpen (box b γ) := by
  have e : box b γ = ⋂ i, (fun x : E => b.repr x i) ⁻¹' {a : K | valuation K a ≤ γ i} := by
    ext x
    simp [box]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_ball (γ i) (hγ i)).preimage (continuous_coord b i)

/- English proof (translation)
Establish `hr : ∀ y : ι → K, b.repr (b.equivFun.symm y) = y` using `fun y => by`. Establish `h1` using `b.equivFun.apply_symm_apply y`. Rewrite `h1` using `[Basis.equivFun_apply]`. Conclude with `h1`. Use extensionality with `x`.

Simplify using `only [box, Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨b.equivFun x, fun i => by simpa [Basis.equivFun_apply] using h i, by simp⟩`. Introduce and unpack `⟨y, hy, rfl⟩ i`.

Rewrite using `[hr]`. Conclude with `hy i`.
-/
theorem box_eq_image (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) :
    box b γ = b.equivFun.symm '' Set.univ.pi (fun i => {a : K | valuation K a ≤ γ i}) := by
  have hr : ∀ y : ι → K, b.repr (b.equivFun.symm y) = y := fun y => by
    have h1 := b.equivFun.apply_symm_apply y
    rw [Basis.equivFun_apply] at h1
    exact h1
  ext x
  simp only [box, Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h
    exact ⟨b.equivFun x, fun i => by simpa [Basis.equivFun_apply] using h i, by simp⟩
  · rintro ⟨y, hy, rfl⟩ i
    rw [hr]
    exact hy i

/- English proof (translation)
Rewrite using `[box_eq_image]`. Conclude with `(isCompact_univ_pi fun i => isCompact_ball (γ i)).image (continuous_equivFun_symm b)`.
-/
theorem isCompact_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : IsCompact (box b γ) := by
  rw [box_eq_image]
  exact (isCompact_univ_pi fun i => isCompact_ball (γ i)).image (continuous_equivFun_symm b)

/- English proof (translation)
Introduce `i`. Simplify using the standard rewrite rules.
-/
theorem zero_mem_box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : (0 : E) ∈ box b γ := by
  intro i
  simp

/- English proof (translation)
Set `e : E ≃ₜ (ι → K)` to `{ toEquiv := b.equivFun.toEquiv continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap continuous_invFun := continuous_equivFun_symm b }`. Conclude with `e.isOpenEmbedding.locallyCompactSpace`.
-/
theorem locallyCompact (b : Basis ι K E) : LocallyCompactSpace E := by
  let e : E ≃ₜ (ι → K) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
      continuous_invFun := continuous_equivFun_symm b }
  exact e.isOpenEmbedding.locallyCompactSpace

def homeo (b : Basis ι K E) : E ≃ₜ (ι → K) where
  toEquiv := b.equivFun.toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
  continuous_invFun := continuous_equivFun_symm b

/- English proof (translation)
Use `haveI := secondCountable K`. Conclude with `(homeo b).isEmbedding.secondCountableTopology`.
-/
theorem secondCountableE (b : Basis ι K E) : SecondCountableTopology E := by
  haveI := secondCountable K
  exact (homeo b).isEmbedding.secondCountableTopology

def toCLE (T : E ≃ₗ[K] E) : E ≃L[K] E :=
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd K E
  { T with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) T.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (R := K) T.symm.toLinearMap }

variable [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Use `haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E`. Use `haveI := locallyCompact b`. Use `haveI := secondCountableE b`. Set `L` to `toCLE T`. Use `haveI : (μ.map L.symm).IsAddHaarMeasure := L.symm.isAddHaarMeasure_map μ`.

Use `⟨addHaarScalarFactor (μ.map L.symm) μ, fun S => ?_⟩` and prove the remaining obligations. Establish `h` using `isAddLeftInvariant_eq_smul (μ.map L.symm) μ`. Establish `h2 : (μ.map L.symm) S = μ (T '' S)`. Establish `hm : (μ.map L.symm) = μ.map (L.symm.toHomeomorph.toMeasurableEquiv)` using `rfl`. Rewrite using `[hm, MeasurableEquiv.map_apply]`.

Establish `hL : ∀ x, L.symm x = T.symm x` using `fun x => rfl`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph, hL, Set.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx; exact ⟨T.symm x, hx, by simp⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`. Establish `h' : (μ.map L.symm) S = _` using `DFunLike.congr_fun h S`. Rewrite using `[← h2, h']`.

Apply the tactic sequence `first | rfl | exact (nnreal_smul_coe_apply _ _ _) | simp`.
-/
theorem image_eq_smul (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E) :
    ∃ c : ℝ≥0, ∀ S : Set E, μ (T '' S) = c * μ S := by
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup K E
  haveI := locallyCompact b
  haveI := secondCountableE b
  let L := toCLE T
  haveI : (μ.map L.symm).IsAddHaarMeasure := L.symm.isAddHaarMeasure_map μ
  refine ⟨addHaarScalarFactor (μ.map L.symm) μ, fun S => ?_⟩
  have h := isAddLeftInvariant_eq_smul (μ.map L.symm) μ
  have h2 : (μ.map L.symm) S = μ (T '' S) := by
    have hm : (μ.map L.symm) = μ.map (L.symm.toHomeomorph.toMeasurableEquiv) := rfl
    rw [hm, MeasurableEquiv.map_apply]
    have hL : ∀ x, L.symm x = T.symm x := fun x => rfl
    congr 1
    ext x
    simp only [Set.mem_preimage, Homeomorph.toMeasurableEquiv_coe,
      ContinuousLinearEquiv.coe_toHomeomorph, hL, Set.mem_image]
    constructor
    · intro hx; exact ⟨T.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  have h' : (μ.map L.symm) S = _ := DFunLike.congr_fun h S
  rw [← h2, h']
  first | rfl | exact (nnreal_smul_coe_apply _ _ _) | simp

/- English proof (translation)
Take `⟨c', hc'⟩` from `image_eq_smul b μ T`. Establish `hpos : μ (box b γ) ≠ 0` using `(isOpen_box b γ hγ).measure_ne_zero μ ⟨0, zero_mem_box b γ⟩`. Establish `hfin : μ (box b γ) ≠ ⊤` using `(isCompact_box b γ).measure_lt_top.ne`. Rewrite `hc` using `[hc' (box b γ)]`. Establish `hcc : ((c' : ℝ≥0∞)) = c` using `(ENNReal.mul_left_inj hpos hfin).mp hc`.

Rewrite using `[hc' S, hcc]`.
-/
theorem image_eq_of_box (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E)
    (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) (c : ℝ≥0∞)
    (hc : μ (T '' box b γ) = c * μ (box b γ)) (S : Set E) : μ (T '' S) = c * μ S := by
  obtain ⟨c', hc'⟩ := image_eq_smul b μ T
  have hpos : μ (box b γ) ≠ 0 := (isOpen_box b γ hγ).measure_ne_zero μ ⟨0, zero_mem_box b γ⟩
  have hfin : μ (box b γ) ≠ ⊤ := (isCompact_box b γ).measure_lt_top.ne
  rw [hc' (box b γ)] at hc
  have hcc : ((c' : ℝ≥0∞)) = c := (ENNReal.mul_left_inj hpos hfin).mp hc
  rw [hc' S, hcc]

end PI.ProdFormulaE.HaarBox
