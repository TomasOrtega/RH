import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BasicOperatorsPolynomialLiftNoInversePower
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HatNF.basicLiftAll_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FBasicOperatorsPolynomialLiftNoInversePower.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.basicOperators_polynomialLift_no_inversePower : BasicLiftAll (fun _ => 0) := by
  first | exact @GlobalTheory.HatNF.basicLiftAll_zero | exact GlobalTheory.HatNF.basicLiftAll_zero | (intros; apply GlobalTheory.HatNF.basicLiftAll_zero <;> assumption)
