import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol.ScaleExists

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trueScale_isScale : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) :=
  GlobalTheory.Mem.Vol.Scale.cdScaleIs_trueScale

end GlobalTheory.Mem.Vol.ScaleExists
