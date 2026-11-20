import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSplitPartAgreeSupportedAtSplitPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitSplit.eq_of_split_part` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FEqOfSplitPartAgreeSupportedAtSplitPlace.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.eq_of_splitPart_agree_supportedAtSplitPlace : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h → SuppAt e S h' →
    (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  first | exact @GlobalTheory.UnitSplit.eq_of_split_part | exact GlobalTheory.UnitSplit.eq_of_split_part | (intros; apply GlobalTheory.UnitSplit.eq_of_split_part <;> assumption)
