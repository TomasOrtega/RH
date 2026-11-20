import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRowOfDictionaryDepth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PairIntRatKOfThetaLocalInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRowOfDictionaryDepthStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open GlobalTheory.SumSize
namespace GlobalTheory.SumSize
/- English proof (translation)
Establish `hG : PairInt.PairIntRatK` using `_root_.GlobalTheory.T.pairIntRatK_of_thetaLocalInputs hP hI hD`. Take `⟨CF0, h⟩` from `BigC.and hG hd`. Use `⟨CF0, fun CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, h⟩` from `h CF hCF`. Use `⟨C0, fun ε C hC => ?_⟩` and prove the remaining obligations.

Take `⟨x0, h⟩` from `h ε C hC`. Use `⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩` and prove the remaining obligations. Take `⟨⟨dl, hL, h⟩, hDe⟩` from `h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3`. Use `⟨dl, hL, ?_⟩` and prove the remaining obligations. Introduce `t w hw Φ β d hO c i a v hv`.

Take `⟨hβ, τ, hτ, hdτ⟩` from `hO`. Establish `hrat` using `(h3.isRatAt hβ hτ hdτ c).2 i`. Take `⟨hk, ⟨e, -, hPz, -⟩, hcos⟩` from `hτ`. Establish `hdep` using `(hDe t Φ β hβ).2`. Conclude with `h t (.chi i D.R.m) ⟨i.2, rfl⟩ w hw _ (d.2 i) hk ((hcos d hdτ).2 i) ((hPz d hdτ).2 i).2.2 ((hPz d hdτ).2 i).1 (fun l hl hlw => hdep w l hl hlw hw) _ _ hrat a v hv`.
-/
theorem finite_place_sum_size_bound (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hD : DictK) (hd : DepthK) : FinRowK := by
  have hG : PairInt.PairIntRatK := _root_.GlobalTheory.T.pairIntRatK_of_thetaLocalInputs hP hI hD
  obtain ⟨CF0, h⟩ := BigC.and hG hd
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C hC
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨⟨dl, hL, h⟩, hDe⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  refine ⟨dl, hL, ?_⟩
  intro t w hw Φ β d hO c i a v hv
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hO
  have hrat := (h3.isRatAt hβ hτ hdτ c).2 i
  obtain ⟨hk, ⟨e, -, hPz, -⟩, hcos⟩ := hτ
  have hdep := (hDe t Φ β hβ).2
  exact h t (.chi i D.R.m) ⟨i.2, rfl⟩ w hw _ (d.2 i) hk ((hcos d hdτ).2 i) ((hPz d hdτ).2 i).2.2 ((hPz d hdτ).2 i).1
    (fun l hl hlw => hdep w l hl hlw hw) _ _ hrat a v hv
end GlobalTheory.SumSize
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.SumSize.finite_place_sum_size_bound | exact _root_.GlobalTheory.SumSize.finite_place_sum_size_bound | (intros; apply _root_.GlobalTheory.SumSize.finite_place_sum_size_bound <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.sum_size_bound_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinRowK := by
  first | exact @_root_.GlobalTheory.SumSize.finite_place_sum_size_bound | exact _root_.GlobalTheory.SumSize.finite_place_sum_size_bound | (intros; apply _root_.GlobalTheory.SumSize.finite_place_sum_size_bound <;> assumption)
end
