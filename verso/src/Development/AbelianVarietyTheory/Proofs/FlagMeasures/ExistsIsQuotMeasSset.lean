import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeil
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

/- English proof (translation)
Introduce `k r z μG μS hz hT hG hS`. Take `⟨μW, hW⟩` from `Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT`. Take `⟨μN, hN⟩` from `Formalism.FourierDecayAlt.P.unipotent_haar_exists k r`. Establish `conv : ∀ {U : Set (Mat k r)} {μ : Measure (Mt k r)}, Formalism.FourierDecayAlt.B.IsHaarOn U μ → IsHaarOn U μ`. Introduce `U μ h`.

Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩`. Conclude with `⟨inferInstance, h.ne_zero, h.conc, h.left⟩`. Take `⟨hSg, hsub, hH, hR⟩` from `GlobalTheory.muSof_isHaar k r z μW μN hz hT (conv hW) (conv hN)`. Establish `hS' : PI.IsHaarOnM (Sset k r z) μS` using `hS`. Take `⟨c, -, -, hc⟩` from `(GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _ hSg hH).1 μS hS'`.

Establish `hR' : PI.IsRightInvM (Sset k r z) μS`. Introduce `s hs`. Rewrite using `[hc, Measure.map_smul, hR s hs]`. Take `⟨hGg, hGH⟩` from `GlobalTheory.unitaryGroup_matGroup_unimodular k r`. Conclude with `GlobalTheory.QuotWeil.exists_isQuotM _ _ _ μG μS hGg hSg hsub (hGH μG hG).1 hS' hR'`.
-/
theorem exists_isQuotMeas_Sset : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (GG k r) μG → IsHaarOn (Sset k r z) μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r z μG μS hz hT hG hS
  obtain ⟨μW, hW⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μN, hN⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have conv : ∀ {U : Set (Mat k r)} {μ : Measure (Mt k r)}, Formalism.FourierDecayAlt.B.IsHaarOn U μ → IsHaarOn U μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩
  obtain ⟨hSg, hsub, hH, hR⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT
    (conv hW) (conv hN)
  have hS' : PI.IsHaarOnM (Sset k r z) μS := hS
  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _ hSg hH).1 μS hS'
  have hR' : PI.IsRightInvM (Sset k r z) μS := by
    intro s hs
    rw [hc, Measure.map_smul, hR s hs]
  obtain ⟨hGg, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  exact GlobalTheory.QuotWeil.exists_isQuotM _ _ _ μG μS hGg hSg hsub (hGH μG hG).1 hS' hR'

end GlobalTheory.SgInf
