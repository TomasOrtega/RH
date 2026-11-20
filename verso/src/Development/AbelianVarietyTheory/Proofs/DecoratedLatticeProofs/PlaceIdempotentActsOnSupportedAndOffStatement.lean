import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FPlaceIdempotentActsOnSupportedAndOff.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff : ∀ (D : D7) (v : Pl D) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ a : AE D, a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) ε * a = a) ∧
    (∀ a : AE D, a ∈ idAt D (· ≠ v) → algebraMap (AF D.host.F) (AE D) ε * a = 0) := by
  first | exact @GlobalTheory.FinPl.placeIdem_acts | exact GlobalTheory.FinPl.placeIdem_acts | (intros; apply GlobalTheory.FinPl.placeIdem_acts <;> assumption)
