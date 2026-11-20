import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamAbelianStructureOfStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations

set_option autoImplicit false

namespace GlobalTheory

/- English proof (translation)
Introduce `hH`. Take `⟨⟨hfree, -, hbc⟩, hcrys⟩` from `GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH`. Establish `hF : GlobalTheory.Published.AbelianDeRham.Free` using `GlobalTheory.AbelianPrim.abelianDeRham_free hfree`. Conclude with `⟨hF, hbc, GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys⟩`.
-/
theorem abelianDeRham_free_baseChange_rigid : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.BaseChange ∧
      GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro hH
  obtain ⟨⟨hfree, -, hbc⟩, hcrys⟩ :=
    GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH
  have hF : GlobalTheory.Published.AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hfree
  exact ⟨hF, hbc, GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys⟩

end GlobalTheory
