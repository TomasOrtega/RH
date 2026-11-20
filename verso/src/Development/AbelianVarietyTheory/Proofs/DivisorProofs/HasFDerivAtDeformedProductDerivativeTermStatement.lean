import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtDeformedProductDerivativeTerm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasFDerivAtDeformedProductDerivativeTerm.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.hasFDerivAt_deformedProductDerivativeTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x) (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by
  first | exact @GlobalTheory.DeformedSum.hasFDerivAt_dTerm | exact GlobalTheory.DeformedSum.hasFDerivAt_dTerm | (intros; apply GlobalTheory.DeformedSum.hasFDerivAt_dTerm <;> assumption)
