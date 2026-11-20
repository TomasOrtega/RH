import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan

namespace GlobalTheory.Published

/- English proof (translation)
Use `hF.toroidalCharts fun E _ _ _ H q => ?_` and prove the remaining obligations. Take `⟨φs, hφ, -⟩` from `hS (Module.finrank ℚ E * q + 1) (Nat.le_add_left _ _)`. Take `⟨φ, h₁, h₂, -⟩` from `GlobalTheory.PolFan.exists_fine_invariant_fan H hφ (Nat.le_succ _) ∅ (by simp)`. Conclude with `⟨φ, h₁, h₂⟩`.
-/
theorem toroidalCharts_of_siegel_of_forFan (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hF : GlobalTheory.Published.ToroidalChartsForFan) :
    GlobalTheory.Published.ToroidalCharts := by
  refine hF.toroidalCharts fun E _ _ _ H q => ?_
  obtain ⟨φs, hφ, -⟩ := hS (Module.finrank ℚ E * q + 1) (Nat.le_add_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hφ (Nat.le_succ _) ∅ (by simp)
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.Published
