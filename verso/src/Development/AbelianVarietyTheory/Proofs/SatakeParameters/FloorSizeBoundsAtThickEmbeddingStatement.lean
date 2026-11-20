import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbedding
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.SizeThick.size_thick` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FFloorSizeBoundsAtThickEmbedding.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.floor_size_bounds_at_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m), Thick D.host g → L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  first | exact @GlobalTheory.HTW.SizeThick.size_thick | exact GlobalTheory.HTW.SizeThick.size_thick | (intros; apply GlobalTheory.HTW.SizeThick.size_thick <;> assumption)
