import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinConstantTermPartialZeta
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisConstTerm.hasSum_constTerm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasSumHilbertEisensteinConstantTermPartialZeta.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (s : ℕ), 1 ≤ s →
  ∀ (D : (Ideal (NumberField.RingOfIntegers F))⁰), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) →
  ∀ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) Z →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 = 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 (2 * s) 0 z c)
      (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F * GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) * Z ((2 * s : ℕ) : ℂ)) := by
  first | exact @GlobalTheory.EisConstTerm.hasSum_constTerm | exact GlobalTheory.EisConstTerm.hasSum_constTerm | (intros; apply GlobalTheory.EisConstTerm.hasSum_constTerm <;> assumption)
