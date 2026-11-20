import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinTrig.loc_chars` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsTrigPolynomialAnnihilatingAdelicSchwartz.lean&line=190#L190)
-/
theorem _root_.GlobalTheory.T.exists_trigPolynomial_annihilating_adelicSchwartz : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) →
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, ∀ i, evI F (q i) = 0) ∧
      ∑ q ∈ s, c q * ψ (y ⬝ᵥ q) = 1 ∧ ∀ x, (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x = 0 := by
  first | exact @GlobalTheory.FinTrig.loc_chars | exact GlobalTheory.FinTrig.loc_chars | (intros; apply GlobalTheory.FinTrig.loc_chars <;> assumption)
