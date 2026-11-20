import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory.SplitProj

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem proj_eq_lift_compAt (L : Type) [Field L] [NumberField L] (s : SplitPlace L) (x : AL L) :
    s.proj x = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) (compAt L s.v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem proj_eq_zero_of_compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] (s : ReciprocityTheory.Aut.SplitPlace L)
    (a : ReciprocityTheory.Aut.AL L), ReciprocityTheory.Aut.compAt L s.v a = 0 → s.proj a = 0 := by
  intro L _ _ s a h
  rw [proj_eq_lift_compAt, h, map_zero]

end GlobalTheory.SplitProj
