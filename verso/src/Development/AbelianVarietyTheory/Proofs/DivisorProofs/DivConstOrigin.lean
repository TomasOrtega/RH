import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleStageDivisorStrictHenselisationOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoethStatement

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

/- English proof (translation)
Establish `h₁` using `GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin`. Establish `h₂` using `GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants`. Establish `h₃` using `GlobalTheory.T.divConst_origin_noeth_alt`. Unfold `GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith GlobalTheory.VertUnits.DivConst`. Introduce `T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh _ hPo b c s hs hbc`.

Establish `hPo' : P = GlobalTheory.KeyOriginCut.originIdeal T` using `hPo`. Take `⟨E, _, _, _, _, _, Q, _, hQ, j, hj, b₁, c₁, hbc₁, hjb, hjc⟩` from `h₁ T O hT P φ hφ hsh hPo' b c s hs hbc`. Take `⟨A, _, _, _, _, _, _, i, hi, hil, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, bA, cA, sA, hsA, hisA, hbcA, hjbA⟩` from `h₂ T O hT E Q hQ j hj b₁ c₁ s hs hbc₁`. Take `⟨a, w, haw⟩` from `h₃ T O hT P φ hφ hsh hPo' A i hi hil EA QA hQA jA hjA bA cA sA hsA hbcA`. Conclude with `⟨a, w, by rw [← hjb, ← hjbA, haw]⟩`.
-/
theorem divConstOrigin : GlobalTheory.VertUnits.DivConstOrigin := by
  have h₁ := GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin
  have h₂ := GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants
  have h₃ := GlobalTheory.T.divConst_origin_noeth_alt
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith GlobalTheory.VertUnits.DivConst
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh _ hPo b c s hs hbc
  have hPo' : P = GlobalTheory.KeyOriginCut.originIdeal T := hPo
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, b₁, c₁, hbc₁, hjb, hjc⟩ :=
    h₁ T O hT P φ hφ hsh hPo' b c s hs hbc
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, bA, cA, sA, hsA, hisA,
    hbcA, hjbA⟩ := h₂ T O hT E Q hQ j hj b₁ c₁ s hs hbc₁
  obtain ⟨a, w, haw⟩ := h₃ T O hT P φ hφ hsh hPo' A i hi hil EA QA hQA jA hjA bA cA sA hsA hbcA
  exact ⟨a, w, by rw [← hjb, ← hjbA, haw]⟩

end GlobalTheory.VertUnits
