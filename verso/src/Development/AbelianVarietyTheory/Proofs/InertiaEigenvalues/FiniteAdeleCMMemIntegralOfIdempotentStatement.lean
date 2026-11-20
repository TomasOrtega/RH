import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictHalfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteAdeleCMMemIntegralOfIdempotent.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.finiteAdeleCM_mem_integral_of_idempotent : ∀ {D : D7} {e : AE D}, e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem | exact GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem | (intros; apply GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem <;> assumption)
