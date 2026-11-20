import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineQuotientTensorDual
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RegularRing.quot_tensor_dual_crys` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCrystallineQuotientTensorDual.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.crystalline_quotient_tensor_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocQuotCrys l P ∧ GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocTensorCrys l P ∧ GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocDualCrys l P := by
  first | exact @GlobalTheory.RegularRing.quot_tensor_dual_crys | exact GlobalTheory.RegularRing.quot_tensor_dual_crys | (intros; apply GlobalTheory.RegularRing.quot_tensor_dual_crys <;> assumption)
