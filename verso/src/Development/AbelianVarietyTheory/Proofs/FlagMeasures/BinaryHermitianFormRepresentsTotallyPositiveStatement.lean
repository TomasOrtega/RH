import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive
import Formalism.HermitianLattices.StatementMass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBinaryHermitianFormRepresentsTotallyPositive.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.binaryHermitianForm_represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n → (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) → ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  first | exact @GlobalTheory.BinaryRep.represents_totallyPositive | exact GlobalTheory.BinaryRep.represents_totallyPositive | (intros; apply GlobalTheory.BinaryRep.represents_totallyPositive <;> assumption)
