import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Th.isCuspFun_closed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsCuspFunctionClosedUnderOperations.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isCuspFunction_closed_under_operations : ∀ (D : D7) (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFun V φ → IsAutFun V φ' → IsCuspFun V φ → IsCuspFun V φ' → IsCuspFun V (φ + φ') ∧ (∀ c : ℂ, IsCuspFun V (c • φ)) ∧ (∀ k, IsCuspFun V (rTr V k φ)) ∧ IsCuspFun V (fun g => star (φ g)) := by
  first | exact @GlobalTheory.Mem.Th.isCuspFun_closed | exact GlobalTheory.Mem.Th.isCuspFun_closed | (intros; apply GlobalTheory.Mem.Th.isCuspFun_closed <;> assumption)
