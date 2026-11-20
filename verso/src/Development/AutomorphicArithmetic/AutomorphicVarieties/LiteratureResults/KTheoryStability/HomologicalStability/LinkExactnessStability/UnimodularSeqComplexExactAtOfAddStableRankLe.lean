import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtUnimodularSeqsOfAddStableRankLe
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uniSeq_exactAt_stableRange : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s →
    ∀ m q : ℕ, q + s ≤ m → ExactAt (uniSeq R m) q :=
  GlobalTheory.T.exactAt_unimodularSeqs_of_add_stableRank_le

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.T.unimodularSeqComplex_exactAt_of_add_stableRank_le : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ m q : ℕ, q + s ≤ m → ExactAt (uniSeq R m) q := by
  first
  | exact @GlobalTheory.uniSeq_exactAt_stableRange
  | exact @GlobalTheory.rests
end
