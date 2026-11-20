import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotient
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FRationalFractionsRepresentPrimeNormQuotient.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.rationalFractions_represent_primeNormQuotient : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  first | exact @GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | exact GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | (intros; apply GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps <;> assumption)
