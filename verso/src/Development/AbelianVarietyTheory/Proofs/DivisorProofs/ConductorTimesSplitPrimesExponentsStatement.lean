import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorTimesSplitPrimesExponents
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMVal.CondExp.condQ_exponents` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConductorTimesSplitPrimesExponents.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.conductorTimesSplitPrimes_exponents : ∀ (E : Type) [Field E] [NumberField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → condQ 𝔣 Q ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → Splits v) ∧ (∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q) ∧ (∀ v ∈ Q, expIn (condQ 𝔣 Q) v = 1) ∧ (∀ v ∉ Q, expIn (condQ 𝔣 Q) v = expIn 𝔣 v) ∧ {v : HeightOneSpectrum (OF E) | expIn (condQ 𝔣 Q) v ≠ 0}.Finite := by
  first | exact @GlobalTheory.CMVal.CondExp.condQ_exponents | exact GlobalTheory.CMVal.CondExp.condQ_exponents | (intros; apply GlobalTheory.CMVal.CondExp.condQ_exponents <;> assumption)
