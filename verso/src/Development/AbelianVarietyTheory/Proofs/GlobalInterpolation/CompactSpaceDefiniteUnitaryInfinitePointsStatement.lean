import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePoints
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InfUCompact.compactSpace_infU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FCompactSpaceDefiniteUnitaryInfinitePoints.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.compactSpace_definiteUnitaryInfinitePoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), CompactSpace (infU E n) := by
  first | exact @GlobalTheory.InfUCompact.compactSpace_infU | exact GlobalTheory.InfUCompact.compactSpace_infU | (intros; apply GlobalTheory.InfUCompact.compactSpace_infU <;> assumption)
