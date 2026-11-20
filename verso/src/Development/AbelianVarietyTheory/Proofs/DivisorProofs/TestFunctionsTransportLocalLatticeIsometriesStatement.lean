import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionsTransportLocalLatticeIsometries
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTestFunctionsTransportLocalLatticeIsometries.lean&line=170#L170)
-/
theorem _root_.GlobalTheory.T.testFunctions_transport_localLatticeIsometries : ∀ (D : D7) (V V' : HSp D), V'.rank = V.rank → ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) → (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ (T' : TypeDataG V') (U' : AuxiliaryPlaceHermitianSpace V'), (NoFixed T → NoFixed T') ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) ff, IsTestFin T U μf ff → IsTestFin T' U' (fun v => (μf v).map (j v)) (transfer j ff) := by
  first | exact @GlobalTheory.LatTransport.isTestFin_transport | exact GlobalTheory.LatTransport.isTestFin_transport | (intros; apply GlobalTheory.LatTransport.isTestFin_transport <;> assumption)
