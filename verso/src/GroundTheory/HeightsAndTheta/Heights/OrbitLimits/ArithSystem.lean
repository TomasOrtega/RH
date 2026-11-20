import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIMultilin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithIntersectionSystem

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem multilin_of_isFamily {I : AllFam} (hI : I.IsFamily) : IsMultilinFam I := by
  intro K _ ι _ P n L j A B hP hL hA hB
  cases n with
  | zero => exact j.elim0
  | succ m =>
    obtain ⟨hsym, hadd, -⟩ := hI K ι
    have e : ∀ X : HermLine ι, IsSmoothHerm X →
        I K ι P (m + 1) (Function.update L j X) =
          I K ι P (m + 1)
            (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
      intro X hX
      rw [← GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.update_comp_swap]
      exact (hsym P (m + 1) _ _ hP
        (GroundTheory.Heights₂.Heights.Inter.ThmIMultilin.smooth_update hL j hX)).symm
    rw [e _ (isSmoothHerm_tensor hA hB), e A hA, e B hB]
    exact hadd P m _ A B hP (fun i => hL _) hA hB

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem of_found (hE : GroundTheory.Heights₂.Heights.Inter.ThmIExists.Statement) (hPF : PFCoordStatement)
    (hCM : ContractMixedStatement) : ArithIntersectionSystemStatement := by
  obtain ⟨I, hI⟩ := (hE : ExistsStatement)
  exact ⟨I, hI, multilin_of_isFamily hI, hPF I hI, hCM I hI⟩

end ArithIntersectionSystem

end GroundTheory.Heights₂.Heights.Targets
