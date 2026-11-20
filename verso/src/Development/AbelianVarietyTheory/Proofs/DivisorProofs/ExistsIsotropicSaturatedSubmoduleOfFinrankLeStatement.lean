import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedSubmoduleOfFinrankLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsotropicSaturatedSubmoduleOfFinrankLe.lean&line=133#L133)
-/
theorem _root_.GlobalTheory.T.exists_isotropicSaturatedSubmodule_of_finrank_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (r : ℕ), r ≤ min D.p D.q →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = r := by
  first | exact @GlobalTheory.LowFilt.exists_isIsoSat_finrank | exact GlobalTheory.LowFilt.exists_isIsoSat_finrank | (intros; apply GlobalTheory.LowFilt.exists_isIsoSat_finrank <;> assumption)
