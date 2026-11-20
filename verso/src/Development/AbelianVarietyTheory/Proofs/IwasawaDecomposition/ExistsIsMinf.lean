import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaarStatement

open Formalism.BasicNotions Formalism.IndefR MeasureTheory

namespace GlobalTheory.MinfMeasure

/- English proof (translation)
The claim follows from `exists_isMinf_of_cd GlobalTheory.T.nonempty_compactDualHaar`.
-/
theorem exists_isMinf : ∀ p q : ℕ, ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  exists_isMinf_of_cd GlobalTheory.T.nonempty_compactDualHaar

end GlobalTheory.MinfMeasure
