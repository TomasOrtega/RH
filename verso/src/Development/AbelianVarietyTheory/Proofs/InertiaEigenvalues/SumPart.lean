import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.UnitsOfFieldDD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal

namespace GlobalTheory.WachSum

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem sumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumPart l P H := by
  intro K s LL h
  exact GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumFor_of_crys fun _ _ _ i i' hs hT hT' =>
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_isSumLat i i' hT hT' hs

end GlobalTheory.WachSum
