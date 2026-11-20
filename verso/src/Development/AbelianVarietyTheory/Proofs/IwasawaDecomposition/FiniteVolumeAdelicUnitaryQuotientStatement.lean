import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFiniteVolumeAdelicUnitaryQuotient.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.finiteVolume_adelicUnitaryQuotient : FiniteVolume₂ := by
  first | exact @GlobalTheory.Mem.VolFin.finVol | exact GlobalTheory.Mem.VolFin.finVol | (intros; apply GlobalTheory.Mem.VolFin.finVol <;> assumption)
