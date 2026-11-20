import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2

noncomputable section

namespace UpperTheory.Gal.TP.Loc

/- English proof (translation)
Introduce `K _ _ w n V _ _ ρ B h`. Use `UpperTheory.V.InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun g x => ?_) h` and prove the remaining obligations. Establish `hg : GlobalTheory.SplitFlip.invT g = GlobalTheory.CuspRep.invT n _ g` using `Units.ext rfl`. Express the relevant statement in the definitionally equal form `ρ (GlobalTheory.SplitFlip.invT g) x = ρ (GlobalTheory.CuspRep.invT n _ g) x`. Rewrite using `[hg]`.
-/
theorem satInvT : SatInvT := by
  intro K _ _ w n V _ _ ρ B h
  refine UpperTheory.V.InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun g x => ?_) h
  have hg : GlobalTheory.SplitFlip.invT g = GlobalTheory.CuspRep.invT n _ g := Units.ext rfl
  change ρ (GlobalTheory.SplitFlip.invT g) x = ρ (GlobalTheory.CuspRep.invT n _ g) x
  rw [hg]

end UpperTheory.Gal.TP.Loc

end
