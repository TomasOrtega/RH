import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBesselPeriodSesquilinear
import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RootExch.PosLinear.posLin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDefiniteBesselPeriodSesquilinear.lean&line=347#L347)
-/
theorem _root_.GlobalTheory.T.definiteBesselPeriod_sesquilinear : ∀ D : D7, PosLin D := by
  first | exact @GlobalTheory.RootExch.PosLinear.posLin | exact GlobalTheory.RootExch.PosLinear.posLin | (intros; apply GlobalTheory.RootExch.PosLinear.posLin <;> assumption)
