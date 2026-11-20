import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementarySublatticesOfIndexDegreesQBinomial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatHecke.subElem_degrees` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FElementarySublatticesOfIndexDegreesQBinomial.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.elementarySublatticesOfIndex_degrees_qBinomial : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (L : Lat O K r), subIdx 0 L = {L} ∧ subElem 0 L = {L} ∧ (∀ k, r < k → subElem k L = ∅) ∧ ∀ X : ℂ, ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * ((subElem k L).ncard : ℂ) * X ^ k = ∏ i ∈ Finset.range r, (1 - (qRes O : ℂ) ^ i * X) := by
  first | exact @GlobalTheory.LatHecke.subElem_degrees | exact GlobalTheory.LatHecke.subElem_degrees | (intros; apply GlobalTheory.LatHecke.subElem_degrees <;> assumption)
