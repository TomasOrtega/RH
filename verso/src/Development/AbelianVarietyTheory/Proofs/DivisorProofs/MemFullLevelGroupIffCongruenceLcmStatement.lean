import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFullLevelGroupIffCongruenceLcm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemFullLevelGroupIffCongruenceLcm.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.mem_fullLevelGroup_iff_congruence_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (r : ℕ) (Y : Data E r), GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsSelfDualTr Y → ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧ ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M' • y := by
  first | exact @GlobalTheory.EqCovol.mem_iff_congr_lcm | exact GlobalTheory.EqCovol.mem_iff_congr_lcm | (intros; apply GlobalTheory.EqCovol.mem_iff_congr_lcm <;> assumption)
