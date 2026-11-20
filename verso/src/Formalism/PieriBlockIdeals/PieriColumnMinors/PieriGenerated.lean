import Formalism.PieriBlockIdeals.StatementLP
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightDominantHolds
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightSuccessive
import Formalism.PieriBlockIdeals.PieriColumnMinors.LpcDpartCommEps
import Formalism.PieriBlockIdeals.PieriColumnMinors.GeneratedHighestWeightHolds

namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

/- English proof (translation)
The claim follows from `TowerPieri_of completeReducibility_holds highestWeightDominant_holds`.
-/
theorem tower_pieri : TowerPieri := TowerPieri_of completeReducibility_holds highestWeightDominant_holds

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ _ _ _ EM B lam2 hF h0 n`. Establish `hT` using `tensor_tower K P M q EM B n hF`. Establish `hb` using `tensor_base_case K P M q EM n (fun b => (lam2 b : K)) h0`. Establish `hTP` using `tower_pieri K (Tens (Fin q) P M n) q n (fun j => Dpart K EM j) (epsY K n) (tensForm n B) lam2 hT hb`. Apply `eq_top_iff.mpr` to reduce the goal to its premises.

Rewrite using `[← hTP, Submodule.span_le]`. Introduce and unpack `z ⟨tau, κ, ρ, hp, hcas⟩`. Conclude with `Submodule.mem_iSup_of_mem tau (Submodule.subset_span ⟨κ, ρ, hp, fun j hj => hcas j hj⟩)`.
-/
theorem pieri_rule : Pieri := by
  intro K P M q _ _ _ _ _ _ _ _ EM B lam2 hF h0 n
  have hT := tensor_tower K P M q EM B n hF
  have hb := tensor_base_case K P M q EM n (fun b => (lam2 b : K)) h0
  have hTP := tower_pieri K (Tens (Fin q) P M n) q n (fun j => Dpart K EM j) (epsY K n)
    (tensForm n B) lam2 hT hb
  apply eq_top_iff.mpr
  rw [← hTP, Submodule.span_le]
  rintro z ⟨tau, κ, ρ, hp, hcas⟩
  exact Submodule.mem_iSup_of_mem tau (Submodule.subset_span ⟨κ, ρ, hp, fun j hj => hcas j hj⟩)

/- English proof (translation)
Introduce `K P M q _ _ _ _ _ _ _ _ EM B lam2 hF hgen n`. Conclude with `pieri_rule K P M q EM B lam2 hF (generatedHighestWeight_holds K M q EM B hF _ hgen) n`.
-/
theorem pieri_generated : PieriGenerated := by
  intro K P M q _ _ _ _ _ _ _ _ EM B lam2 hF hgen n
  exact pieri_rule K P M q EM B lam2 hF (generatedHighestWeight_holds K M q EM B hF _ hgen) n

end Formalism.CohomologicalDescent.LP
