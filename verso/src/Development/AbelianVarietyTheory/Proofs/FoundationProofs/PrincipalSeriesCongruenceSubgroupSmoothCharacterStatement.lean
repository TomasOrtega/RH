import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupSmoothCharacter
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsType.grp_theta_datum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrincipalSeriesCongruenceSubgroupSmoothCharacter.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_smoothCharacterDatum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  first | exact @GlobalTheory.PsType.grp_theta_datum | exact GlobalTheory.PsType.grp_theta_datum | (intros; apply GlobalTheory.PsType.grp_theta_datum <;> assumption)
