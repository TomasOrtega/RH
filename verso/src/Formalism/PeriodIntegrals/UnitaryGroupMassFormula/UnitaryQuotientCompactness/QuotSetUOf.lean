import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SsetGroup

open MeasureTheory Matrix

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

/- English proof (translation)
Introduce `k r z hz hT`. Use `⟨hUH k r, hSG k r z hz hT, hSub k r z, ?_, ?_⟩` and prove the remaining obligations. Introduce `μG hμ`. Take `⟨D, hD, hD1⟩` from `hMod _ _ (hUH k r)`. Conclude with `hD1 (hTG k r D hD) μG hμ`.

Introduce `μS hμ`. Take `⟨D, hD, hD1⟩` from `hMod _ _ (hSG k r z hz hT)`. Conclude with `hD1 (hTS k r z hz hT D hD) μS hμ`.
-/
theorem quotSetU_of (hUH : UHGroup) (hSub : SsetSub) (hSG : SsetGroup) (hMod : ModExists)
    (hTG : TrivG) (hTS : TrivS) : PI.QuotSetU := by
  intro k r z hz hT
  refine ⟨hUH k r, hSG k r z hz hT, hSub k r z, ?_, ?_⟩
  · intro μG hμ
    obtain ⟨D, hD, hD1⟩ := hMod _ _ (hUH k r)
    exact hD1 (hTG k r D hD) μG hμ
  · intro μS hμ
    obtain ⟨D, hD, hD1⟩ := hMod _ _ (hSG k r z hz hT)
    exact hD1 (hTS k r z hz hT D hD) μS hμ

end PI.QuotSetU.UnitaryGroupMassFormula
