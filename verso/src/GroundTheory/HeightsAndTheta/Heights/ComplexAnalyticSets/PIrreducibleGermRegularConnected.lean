import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalParametrisation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametrisationSheetsConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem IrreducibleGermRegularConnected.proof (hpar : LocalParametrisation.Statement)
    (hsheets : ParametrisationSheetsConnected.Statement) :
    IrreducibleGermRegularConnected.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, B, D, δ, N, hBU, hP⟩ := hpar σ X w hX hirr U hU
  have hS := hsheets σ X w B d A D δ N hP hirr
  obtain ⟨hBo, hwXB, -, -, -, -, -, -, -, -, hchart, hdense⟩ := hP

  have hSreg : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ regLocus (X ∩ B) := by
    rintro x ⟨hxXB, hx⟩
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hchart x hxXB hx
    exact ⟨hxXB, d, A, O, V, g, hO, hV, hxV, hg, hAg, hXV⟩
  exact ⟨B, hBo, hwXB.2, hBU, hS.subset_closure hSreg ((regLocus_subset _).trans hdense)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
