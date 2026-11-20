import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenPi
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QSA.traceOpen_pi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuaternionNormOneTraceOpenPi.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_pi : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i), (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  first | exact @GlobalTheory.QSA.traceOpen_pi | exact GlobalTheory.QSA.traceOpen_pi | (intros; apply GlobalTheory.QSA.traceOpen_pi <;> assumption)
