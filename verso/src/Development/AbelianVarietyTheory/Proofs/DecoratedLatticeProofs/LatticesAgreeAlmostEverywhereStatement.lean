import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.latV_eq_off_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLatticesAgreeAlmostEverywhere.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.lattices_agree_almost_everywhere : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsLattice D.host.E L → Submodule.IsLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  first | exact @GlobalTheory.FinPl.latV_eq_off_finite | exact GlobalTheory.FinPl.latV_eq_off_finite | (intros; apply GlobalTheory.FinPl.latV_eq_off_finite <;> assumption)
