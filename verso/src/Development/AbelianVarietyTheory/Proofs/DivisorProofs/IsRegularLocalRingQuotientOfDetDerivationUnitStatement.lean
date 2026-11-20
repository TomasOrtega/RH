import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnit
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsRegularLocalRingQuotientOfDetDerivationUnit.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit : ∀ (T : Type) [CommRing T] [IsRegularRing T] (h : ℕ) (f : Fin h → T) (D : Fin h → Derivation ℤ T T) (n : Ideal T) [n.IsPrime], (∀ j, f j ∈ n) → (Matrix.of fun i j => D i (f j)).det ∉ n → IsRegularLocalRing (Localization.AtPrime n ⧸ (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime n))) := by
  first | exact @GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient | exact GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient | (intros; apply GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient <;> assumption)
