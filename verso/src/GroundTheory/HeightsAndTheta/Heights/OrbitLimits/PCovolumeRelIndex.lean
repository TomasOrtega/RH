import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCovolumeRelIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory Module ZLattice

open scoped Classical in

/- English proof (translation)
Introduce `E _ _ _ _ _ μ _ L₁ L₂ _ _ _ _ h`. Set `f : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E` to `(Module.finBasis ℝ E).equivFunL.symm`. Set `ν : Measure (Fin (finrank ℝ E) → ℝ)` to `μ.map f.symm`. Establish `: ν.IsAddHaarMeasure` using `f.symm.isAddHaarMeasure_map μ`. Establish `hf : MeasurePreserving f ν μ`.

Use `⟨f.continuous.measurable, ?_⟩` and prove the remaining obligations. Simplify using `only [ν]`. Rewrite using `[Measure.map_map f.continuous.measurable f.symm.continuous.measurable]`. Establish `: (⇑f ∘ ⇑f.symm) = id` using `by ext x; simp`. Rewrite using `[this, Measure.map_id]`.

Take `⟨c, hν⟩ : ∃ c : NNReal, ν = c • volume` from `⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩`. Establish `scale : ∀ (L : Submodule ℤ (Fin (finrank ℝ E) → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L], covolume L ν = (c : ℝ) * covolume L volume`. Introduce `L _ _`. Rewrite using `[covolume_eq_measure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) ν), covolume_eq_measure_fundamentalDomain L volume (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) volume)]`. Use `conv_lhs => rw [hν]`.

Conclude with `measureReal_nnreal_smul_apply c`. Establish `hidx : ((ZLattice.comap ℝ L₁ f.toLinearMap).toAddSubgroup.relIndex (ZLattice.comap ℝ L₂ f.toLinearMap).toAddSubgroup : ℝ) = (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ)`. Rewrite using `[ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj, LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm', AddSubgroup.comap_equiv_eq_map_symm', AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]`. Establish `key` using `covolume_div_covolume_eq_relIndex (ZLattice.comap ℝ L₁ f.toLinearMap) (ZLattice.comap ℝ L₂ f.toLinearMap) (fun _ h' ↦ h h')`. Establish `hne` using `covolume_ne_zero (ZLattice.comap ℝ L₂ f.toLinearMap) volume`.

Rewrite using `[← covolume_comap L₁ μ ν hf, ← covolume_comap L₂ μ ν hf, scale, scale, ← hidx, ← key]`. Clear the denominators using the available nonvanishing facts.
-/
theorem CovolumeRelIndex.proof : CovolumeRelIndex.Statement := by
  intro E _ _ _ _ _ μ _ L₁ L₂ _ _ _ _ h
  let f : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := (Module.finBasis ℝ E).equivFunL.symm
  let ν : Measure (Fin (finrank ℝ E) → ℝ) := μ.map f.symm
  have : ν.IsAddHaarMeasure := f.symm.isAddHaarMeasure_map μ
  have hf : MeasurePreserving f ν μ := by
    refine ⟨f.continuous.measurable, ?_⟩
    simp only [ν]
    rw [Measure.map_map f.continuous.measurable f.symm.continuous.measurable]
    have : (⇑f ∘ ⇑f.symm) = id := by ext x; simp
    rw [this, Measure.map_id]
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have scale : ∀ (L : Submodule ℤ (Fin (finrank ℝ E) → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
      covolume L ν = (c : ℝ) * covolume L volume := by
    intro L _ _
    rw [covolume_eq_measure_fundamentalDomain L ν
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) ν),
      covolume_eq_measure_fundamentalDomain L volume
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) volume)]
    conv_lhs => rw [hν]
    exact measureReal_nnreal_smul_apply c
  have hidx : ((ZLattice.comap ℝ L₁ f.toLinearMap).toAddSubgroup.relIndex
      (ZLattice.comap ℝ L₂ f.toLinearMap).toAddSubgroup : ℝ) =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
      LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]
  have key := covolume_div_covolume_eq_relIndex (ZLattice.comap ℝ L₁ f.toLinearMap)
    (ZLattice.comap ℝ L₂ f.toLinearMap) (fun _ h' ↦ h h')
  have hne := covolume_ne_zero (ZLattice.comap ℝ L₂ f.toLinearMap) volume
  rw [← covolume_comap L₁ μ ν hf, ← covolume_comap L₂ μ ν hf, scale, scale, ← hidx, ← key]
  field_simp

end GroundTheory.Heights₂.Heights.Targets
