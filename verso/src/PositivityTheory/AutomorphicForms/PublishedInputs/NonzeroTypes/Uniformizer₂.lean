import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open ValuativeRel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Uniformizer₂

/- English proof (translation)
Introduce `h`. Apply `hw` to reduce the goal to its premises. Conclude with `Subtype.ext (by simpa using h)`.
-/
lemma algebraMap_ne_zero {w : 𝒪[k]} (hw : w ≠ 0) : algebraMap 𝒪[k] k w ≠ 0 := by
  intro h
  apply hw
  exact Subtype.ext (by simpa using h)

end Uniformizer₂

/- English proof (translation)
Take `⟨w, hw⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[k]`. Conclude with `⟨Units.mk0 _ (Uniformizer₂.algebraMap_ne_zero hw.ne_zero), w, hw, rfl⟩`.
-/
theorem step_unif : UniformizerProp (k := k) := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  exact ⟨Units.mk0 _ (Uniformizer₂.algebraMap_ne_zero hw.ne_zero), w, hw, rfl⟩

end UpperTheory.TNZ.Grp
