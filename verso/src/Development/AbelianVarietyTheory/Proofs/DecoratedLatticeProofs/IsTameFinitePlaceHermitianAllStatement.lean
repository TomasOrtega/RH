import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.TamePlaces.tame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FIsTameFinitePlaceHermitianAll.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.isTameFinitePlaceHermitian_all : ∀ (D : D7) (v : Pl D), Tame D v := by
  first | exact @GlobalTheory.FinPl.TamePlaces.tame | exact GlobalTheory.FinPl.TamePlaces.tame | (intros; apply GlobalTheory.FinPl.TamePlaces.tame <;> assumption)
