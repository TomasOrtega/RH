import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegral
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
Apply `GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMemCompletedLatticeOfFrameMatrixIntegral.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)}, PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → IsIntM (frMapO S T F.βS F.βT x) → x ∈ F.lat := by
  first | exact @GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int | exact GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int | (intros; apply GlobalTheory.IntHalfLat.mem_lat_of_frMapO_int <;> assumption)
