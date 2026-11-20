import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.DetSqrtCover

/- English proof (translation)
Introduce `p q` and use `⟨grpOf p q MeasureTheory.Measure.haar⟩`.
-/
theorem nonempty_grpData : ∀ p q : ℕ, Nonempty (GrpData p q) :=
  fun p q => ⟨grpOf p q MeasureTheory.Measure.haar⟩

end GlobalTheory.DetSqrtCover
