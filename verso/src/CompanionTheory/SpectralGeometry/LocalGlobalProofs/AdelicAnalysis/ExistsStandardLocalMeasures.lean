import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StdEx

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open NumberField.mixedEmbedding
open scoped TensorProduct ENNReal NNReal Matrix

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem exists_isStdV (v : HeightOneSpectrum (𝓞 F)) : ∃ lam : Measure (Fv F v), IsStdV v lam := by
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hc := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let K : TopologicalSpace.PositiveCompacts (Fv F v) :=
    ⟨⟨(v.adicCompletionIntegers F : Set (Fv F v)), isCompact_iff_compactSpace.2 hc⟩, by
      change (interior (v.adicCompletionIntegers F : Set (Fv F v))).Nonempty
      have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
        Valued.isOpen_valuationSubring _
      rw [hO.interior_eq]
      exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩

omit [NumberField F] in

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

omit [NumberField F] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_span_iff (x : mixedSpace F) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis F)) ↔
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x ∈
        ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom.range := by
  have hk : x ∈ mixedEmbedding.integerLattice F ↔ ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
    simp [LinearMap.mem_range]
  rw [mem_span_latticeBasis, hk]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.injective
    rw [RingEquiv.symm_apply_apply]
    exact ha

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isStdInf : ∃ laminf : Measure (Ainf F), IsStdInf laminf := by
  classical
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hce : Continuous e := continuous_toMixed F
  have hcs : Continuous e.symm := continuous_ofMixed F
  let D₀ : Set (mixedSpace F) := ZSpan.fundamentalDomain (latticeBasis F)
  let μ₀ : Measure (mixedSpace F) := volume
  have h0 : μ₀ D₀ ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero (latticeBasis F)
  have ht : μ₀ D₀ ≠ ∞ := (ZSpan.fundamentalDomain_isBounded (latticeBasis F)).measure_lt_top.ne
  have hD₀ : MeasurableSet D₀ := ZSpan.fundamentalDomain_measurableSet (latticeBasis F)
  let c : ℝ≥0 := ((μ₀ D₀).toNNReal)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (ENNReal.toNNReal_ne_zero.2 ⟨h0, ht⟩)
  let μ₁ : Measure (mixedSpace F) := c • μ₀
  have : μ₁.IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ₀ hc
  have hμ₁ : μ₁ D₀ = 1 := by
    have hv : ((μ₀ D₀).toNNReal : ℝ≥0∞) = μ₀ D₀ := ENNReal.coe_toNNReal ht
    have hne : (μ₀ D₀).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.2 ⟨h0, ht⟩
    change (c • μ₀) D₀ = 1
    rw [Measure.smul_apply, ← hv, ENNReal.smul_def, smul_eq_mul, hv, ← hv, ← ENNReal.coe_mul,
      inv_mul_cancel₀ hne, ENNReal.coe_one]
  let E : Ainf F ≃ᵐ mixedSpace F :=
    (Homeomorph.mk e.toEquiv hce hcs).toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  let lam : Measure (Ainf F) := Measure.map e.symm μ₁
  have hlamE : lam = Measure.map E.symm μ₁ := rfl
  have hmp : MeasurePreserving E lam μ₁ := by
    refine ⟨E.measurable, ?_⟩
    rw [hlamE, Measure.map_map E.measurable E.symm.measurable]
    simp
  refine ⟨lam, ?_, e ⁻¹' D₀, ?_, ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map μ₁ e.symm.toAddEquiv hcs hce
  · have hF₀ := ZSpan.isAddFundamentalDomain (latticeBasis F) μ₁
    refine hF₀.preimage_of_equiv (f := e) hmp.quasiMeasurePreserving
      (e := fun g => ⟨e.symm g.1, (mem_span_iff F g.1).1 g.2⟩) ⟨?_, ?_⟩ ?_
    · intro g h hgh
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val hgh))
    · rintro ⟨y, hy⟩
      refine ⟨⟨e y, (mem_span_iff F (e y)).2 (by
        change e.symm (e y) ∈ _
        rw [e.symm_apply_apply]
        exact hy)⟩, ?_⟩
      exact Subtype.ext (e.symm_apply_apply y)
    · intro g x
      change e (e.symm g.1 + x) = g.1 + e x
      rw [map_add, e.apply_symm_apply]
  · exact (hmp.measure_preimage hD₀.nullMeasurableSet).trans hμ₁

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem exists_std : ∀ (F : Type) [Field F] [NumberField F],
    (∃ laminf : Measure (Ainf F), IsStdInf laminf) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∃ lam : Measure (Fv F v), IsStdV v lam :=
  fun F _ _ => ⟨exists_isStdInf F, exists_isStdV F⟩

end GlobalTheory.CompanionTheory.SW.StdEx
