import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSelfDualTraceForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsotropicIndefiniteSelfDualTraceForm.lean&line=152#L152)
-/
theorem _root_.GlobalTheory.T.exists_isotropic_indefinite_selfDualTraceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ) (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y → ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  first | exact @GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr | exact GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr | (intros; apply GlobalTheory.EqCovol.exists_isotropic_of_isSelfDualTr <;> assumption)
