import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSelfDualLatticesConjugateAtFinitePlace.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.selfDualLattices_conjugate_at_finitePlace : ∀ (D : D7) (V : HSp D) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → ∀ x : Pl D, ∃ g ∈ grpAt V (· = x), Moves V g L M (· = x) := by
  first | exact @GlobalTheory.FinPl.SelfDualConj.conj_at_place | exact GlobalTheory.FinPl.SelfDualConj.conj_at_place | (intros; apply GlobalTheory.FinPl.SelfDualConj.conj_at_place <;> assumption)
