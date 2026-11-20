import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataStateLocalisations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeightCounting.Fin3.MvLoc.exists_moved_loc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsMovedDataStateLocalisations.lean&line=142#L142)
-/
theorem _root_.GlobalTheory.T.exists_movedData_state_localisations : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))), ∃ m : Moved (oL x L), m.z = datL x L ∧ m.Copy ∧ m.Coh := by
  first | exact @GlobalTheory.HeightCounting.Fin3.MvLoc.exists_moved_loc | exact GlobalTheory.HeightCounting.Fin3.MvLoc.exists_moved_loc | (intros; apply GlobalTheory.HeightCounting.Fin3.MvLoc.exists_moved_loc <;> assumption)
