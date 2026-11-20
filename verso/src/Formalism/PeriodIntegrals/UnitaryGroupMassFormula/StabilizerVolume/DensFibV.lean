import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Conclude with `Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective`.
-/
theorem countable_numberField : Countable F := by
  exact Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective

/- English proof (translation)
Use `haveI := countable_numberField F`. Conclude with `⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _, HeightOneSpectrum.denseRange_algebraMap F v⟩⟩`.
-/
theorem separableSpace_Fv : TopologicalSpace.SeparableSpace (Fv F v) := by
  haveI := countable_numberField F
  exact ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
    HeightOneSpectrum.denseRange_algebraMap F v⟩⟩

/- English proof (translation)
Use `haveI := separableSpace_Fv F v`. Conclude with `UniformSpace.secondCountable_of_separable (Fv F v)`.
-/
theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  haveI := separableSpace_Fv F v
  exact UniformSpace.secondCountable_of_separable (Fv F v)

/- English proof (translation)
Establish `hK` using `PI.AdicCompletionValuation.isCompact_adicCompletionIntegers (F := F) (v := v)`. Establish `hN : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∈ 𝓝 (0 : v.adicCompletion F)`. Conclude with `(Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers F).zero_mem`. Conclude with `hK.locallyCompactSpace_of_mem_nhds_of_addGroup hN`.
-/
theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) := by
  have hK := PI.AdicCompletionValuation.isCompact_adicCompletionIntegers (F := F) (v := v)
  have hN : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∈ 𝓝 (0 : v.adicCompletion F) := by
    exact (Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers F).zero_mem
  exact hK.locallyCompactSpace_of_mem_nhds_of_addGroup hN

/- English proof (translation)
Establish `h : {r : Fv F v | IsUnit r} = {0}ᶜ`. Use extensionality with `r`. Simplify using `[isUnit_iff_ne_zero]`. Rewrite using `[h]`. Conclude with `isOpen_compl_singleton`.
-/
theorem isOpen_units_Fv : IsOpen {r : Fv F v | IsUnit r} := by
  have h : {r : Fv F v | IsUnit r} = {0}ᶜ := by
    ext r
    simp [isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton

end Local

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ v μv hμv νv hνv fibV hfib Φv gv hSB hdens`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Use `secondCountable_Fv F v` as an intermediate fact. Use `locallyCompact_Fv F v` as an intermediate fact. Use `hμv.1` as an intermediate fact.

Use `hνv.1` as an intermediate fact. Establish `hσ : ∀ x, σ (σ x) = x` using `sigma_invol σ hCM.2.2.2`. Establish `hN` using `isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a`. Conclude with `DensGen.densGen (B := Set.univ) hfib (continuous_gramH (Fv F v) σ hσ J hJ.1) (fun X => rfl) Subtype.val_injective (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) hSB.1.continuous hSB.2 hdens Filter.univ_mem (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet)) (hN.mem_nhd …`.
-/
theorem densFibV_holds : DensFibV := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ v μv hμv νv hνv fibV hfib Φv gv
    hSB hdens
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  exact DensGen.densGen (B := Set.univ) hfib (continuous_gramH (Fv F v) σ hσ J hJ.1)
    (fun X => rfl) Subtype.val_injective
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX)
    hSB.1.continuous hSB.2 hdens Filter.univ_mem
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))

end PI.VolStabS
