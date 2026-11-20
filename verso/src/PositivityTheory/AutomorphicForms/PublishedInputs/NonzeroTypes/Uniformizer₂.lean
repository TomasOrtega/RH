import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open ValuativeRel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Uniformizer₂

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
lemma algebraMap_ne_zero {w : 𝒪[k]} (hw : w ≠ 0) : algebraMap 𝒪[k] k w ≠ 0 := by
  intro h
  apply hw
  exact Subtype.ext (by simpa using h)

end Uniformizer₂

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem step_unif : UniformizerProp (k := k) := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  exact ⟨Units.mk0 _ (Uniformizer₂.algebraMap_ne_zero hw.ne_zero), w, hw, rfl⟩

end UpperTheory.TNZ.Grp
