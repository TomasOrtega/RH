import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaLebUnique

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem omegaLeb_unique :
    ∀ (P Q : ℕ) (l l' : Measure (lieU P Q)), IsOmegaLeb l → IsOmegaLeb l' → l = l' :=
  fun _ _ _ _ h h' => GlobalTheory.CompactDualUnique.isOmegaLeb_unique h h'

end GlobalTheory.OmegaLebUnique
