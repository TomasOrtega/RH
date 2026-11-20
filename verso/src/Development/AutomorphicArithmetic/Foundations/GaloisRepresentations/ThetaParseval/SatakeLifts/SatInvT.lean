import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2

noncomputable section

namespace UpperTheory.Gal.TP.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem satInvT : SatInvT := by
  intro K _ _ w n V _ _ ρ B h
  refine UpperTheory.V.InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun g x => ?_) h
  have hg : GlobalTheory.SplitFlip.invT g = GlobalTheory.CuspRep.invT n _ g := Units.ext rfl
  change ρ (GlobalTheory.SplitFlip.invT g) x = ρ (GlobalTheory.CuspRep.invT n _ g) x
  rw [hg]

end UpperTheory.Gal.TP.Loc

end
