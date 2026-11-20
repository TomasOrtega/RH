import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
open GlobalTheory.LatHecke GlobalTheory.RowSatakeBound
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIsUnitarySphericalSatakeMultisetMapInv.lean&line=241#L241)
-/
theorem _root_.GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (β : Multiset ℂ), IsUnitarySatake O K r β → IsUnitarySatake O K r (β.map (·⁻¹)) := by
  first | exact @GlobalTheory.SatakeInv.isUnitarySatake_map_inv | exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv | (intros; apply GlobalTheory.SatakeInv.isUnitarySatake_map_inv <;> assumption)
