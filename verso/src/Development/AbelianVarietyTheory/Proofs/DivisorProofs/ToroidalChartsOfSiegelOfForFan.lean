import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan

namespace GlobalTheory.Published

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem toroidalCharts_of_siegel_of_forFan (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hF : GlobalTheory.Published.ToroidalChartsForFan) :
    GlobalTheory.Published.ToroidalCharts := by
  refine hF.toroidalCharts fun E _ _ _ H q => ?_
  obtain ⟨φs, hφ, -⟩ := hS (Module.finrank ℚ E * q + 1) (Nat.le_add_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hφ (Nat.le_succ _) ∅ (by simp)
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.Published
