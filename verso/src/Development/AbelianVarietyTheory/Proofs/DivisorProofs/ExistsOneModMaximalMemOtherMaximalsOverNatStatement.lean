import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneModMaximalMemOtherMaximalsOverNat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.sep_one_mod_maximal_mem_others` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsOneModMaximalMemOtherMaximalsOverNat.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_one_mod_maximal_mem_other_maximals_over_nat : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  first | exact @GlobalTheory.sep_one_mod_maximal_mem_others | exact GlobalTheory.sep_one_mod_maximal_mem_others | (intros; apply GlobalTheory.sep_one_mod_maximal_mem_others <;> assumption)
