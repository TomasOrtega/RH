import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorExponentLeOfIntegral
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DenomBound.cE_le_of_inZl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPartialZetaDenominatorExponentLeOfIntegral.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.partialZetaDenominatorExponent_le_of_integral : ∀ {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime], 2 ≤ a → 1 ≤ n →
    (∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) → cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) := by
  first | exact @GlobalTheory.DenomBound.cE_le_of_inZl | exact GlobalTheory.DenomBound.cE_le_of_inZl | (intros; apply GlobalTheory.DenomBound.cE_le_of_inZl <;> assumption)
