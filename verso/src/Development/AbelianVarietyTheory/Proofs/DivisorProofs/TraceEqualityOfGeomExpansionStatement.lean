import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqualityOfGeomExpansion
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TraceEqTwo.traceEq_of_geomExpansion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraceEqualityOfGeomExpansion.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.trace_equality_of_geom_expansion : GeomExpansion → TraceEq := by
  first | exact @GlobalTheory.TraceEqTwo.traceEq_of_geomExpansion | exact GlobalTheory.TraceEqTwo.traceEq_of_geomExpansion | (intros; apply GlobalTheory.TraceEqTwo.traceEq_of_geomExpansion <;> assumption)
