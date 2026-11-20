import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi

open GlobalTheory.CompanionTheory.SW.RealCoord

section Domain

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def infToMixed (y : Ainf F) : mixedEmbedding.mixedSpace F := toMixed F (coord F y)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem infToMixed_add (x y : Ainf F) : infToMixed F (x + y) = infToMixed F x + infToMixed F y := by
  show toMixed F (coord F (x + y)) = toMixed F (coord F x) + toMixed F (coord F y)
  rw [map_add, toMixed_add]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem infToMixed_algebraMap (x : F) :
    infToMixed F (algebraMap F (Ainf F) x) = mixedEmbedding F x := toMixed_coord_algebraMap F x

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem infToMixed_sub (x y : Ainf F) : infToMixed F (x - y) = infToMixed F x - infToMixed F y := by
  rw [eq_sub_iff_add_eq, ← infToMixed_add, sub_add_cancel]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem measurable_infToMixed : Measurable (infToMixed F) := (measurePreserving_toMixed F).measurable.comp (coord_measurable F)

def infDomain : Set (Ainf F) :=
  infToMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem measurableSet_infDomain : MeasurableSet (infDomain F) := measurable_infToMixed F (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F))

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_mem_lattice {x : mixedEmbedding.mixedSpace F}
    (hx : x ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) :
    ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
  rw [mixedEmbedding.mem_span_latticeBasis F] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_lattice (a : 𝓞 F) :
    mixedEmbedding F (a : F) ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := (mixedEmbedding.mem_span_latticeBasis F).2 ⟨a, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem existsUnique_sub_mem_infDomain (y : Ainf F) :
    ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ infDomain F := by
  obtain ⟨v, hv, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F)
    (infToMixed F y)
  obtain ⟨a, ha⟩ := exists_mem_lattice F (Submodule.neg_mem _ v.2)
  have key : ∀ b : 𝓞 F, infToMixed F (y - algebraMap F (Ainf F) (b : F)) =
      -mixedEmbedding F (b : F) + infToMixed F y := fun b => by
    rw [infToMixed_sub, infToMixed_algebraMap]
    abel
  refine ⟨a, ?_, fun b hb => ?_⟩
  · show infToMixed F (y - algebraMap F (Ainf F) (a : F)) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
    rw [key, ha, neg_neg]
    exact hv
  · have hw := huniq ⟨-mixedEmbedding F (b : F), neg_mem (mem_lattice F b)⟩ (by
      show -mixedEmbedding F (b : F) + infToMixed F y ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
      rw [← key]
      exact hb)
    have hb' : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      have := congrArg Subtype.val hw
      simp only at this
      rw [← this, neg_neg]
    exact RingOfIntegers.ext (mixedEmbedding_injective F hb')

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_isCompact_superset_infDomain :
    ∃ K₀ : Set (Ainf F), IsCompact K₀ ∧ infDomain F ⊆ K₀ := by
  let g : mixedEmbedding.mixedSpace F → (InfinitePlace F → ℝ) := fun x w => x.1 ⟨w, IsTotallyReal.isReal w⟩
  have hg : Continuous g := continuous_pi fun w => (continuous_apply _).comp continuous_fst
  have hC : IsCompact (closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  refine ⟨coord F ⁻¹' (g '' closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))), ?_, ?_⟩
  · rw [← coordHomeo_coe]
    exact (coordHomeo F).isCompact_preimage.2 (hC.image hg)
  · intro y hy
    exact ⟨infToMixed F y, subset_closure hy, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem measure_infDomain (li : Measure (Ainf F)) (hl : IsStdInf li) : li (infDomain F) = 1 := by
  have hfd := ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)
  have hmeas := (measurePreserving_toMixed F).measurable hfd
  have hpos : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))
  have hv : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [mixedEmbedding.volume_fundamentalDomain_latticeBasis, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
      one_mul, ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  calc li (infDomain F)
      = (li.map (coord F)) (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
        (Measure.map_apply (coord_measurable F) hmeas).symm
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [map_coord_eq F li hl, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [(measurePreserving_toMixed F).measure_preimage hfd.nullMeasurableSet]
    _ = 1 := by
        rw [hv, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_mul_cancel₀ hpos.ne',
          ENNReal.ofReal_one]

end Domain

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_bounded_infDomain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧
      li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  intro F _ _ hTR li hl
  have := hTR
  obtain ⟨K₀, hK₀, hsub⟩ := exists_isCompact_superset_infDomain F
  exact ⟨infDomain F, K₀, measurableSet_infDomain F, hK₀, hsub, measure_infDomain F li hl,
    existsUnique_sub_mem_infDomain F⟩

end GlobalTheory.CompanionTheory.Equi

end
