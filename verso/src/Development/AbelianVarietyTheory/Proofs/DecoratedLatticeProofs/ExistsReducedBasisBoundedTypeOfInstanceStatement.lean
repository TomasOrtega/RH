import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstance
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeo.redBasis_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsReducedBasisBoundedTypeOfInstance.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.existsReducedBasisBoundedType_of_instance : ∀ I : AutInst, RedBasis I := by
  first | exact @GlobalTheory.CuspGeo.redBasis_holds | exact GlobalTheory.CuspGeo.redBasis_holds | (intros; apply GlobalTheory.CuspGeo.redBasis_holds <;> assumption)
