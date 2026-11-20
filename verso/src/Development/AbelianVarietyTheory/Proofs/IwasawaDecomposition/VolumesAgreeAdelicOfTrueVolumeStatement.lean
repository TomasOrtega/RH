import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolume
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Vol.volTieG_of_trueVol` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FVolumesAgreeAdelicOfTrueVolume.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.volumesAgreeAdelic_of_trueVolume : ∀ D : D7, letI := D.host.cmStar; (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  first | exact @GlobalTheory.Mem.Vol.volTieG_of_trueVol | exact GlobalTheory.Mem.Vol.volTieG_of_trueVol | (intros; apply GlobalTheory.Mem.Vol.volTieG_of_trueVol <;> assumption)
