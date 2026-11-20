import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFrameMatricesIntegralOfMemCompletedLattice.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)}, PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → x ∈ F.lat → IsIntM (frMapO S T F.βS F.βT x) ∧ IsIntM (frMapAdj S T F.βS F.βT x) := by
  first | exact @GlobalTheory.LatHalfInt.frMap_int_of_mem_lat | exact GlobalTheory.LatHalfInt.frMap_int_of_mem_lat | (intros; apply GlobalTheory.LatHalfInt.frMap_int_of_mem_lat <;> assumption)
