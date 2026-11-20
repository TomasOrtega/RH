import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardResidueFieldLocalOrderUnitaryProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardResidueFieldLocalOrderUnitaryProd.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.card_residueField_localOrder_unitary_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  first | exact @GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any | exact GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any | (intros; apply GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any <;> assumption)
