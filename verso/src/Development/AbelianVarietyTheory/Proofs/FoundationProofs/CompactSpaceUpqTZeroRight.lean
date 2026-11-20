import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqDefiniteCompact

open Formalism.BasicNotions MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem compactSpace_UpqT_zero_right : ∀ N : ℕ, CompactSpace (UpqT N 0) :=
  fun N => (GlobalTheory.compactSpace_UpqT_definite N).1

end GlobalTheory
