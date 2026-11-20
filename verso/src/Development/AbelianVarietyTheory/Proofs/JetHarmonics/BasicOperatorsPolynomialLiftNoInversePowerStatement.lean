import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BasicOperatorsPolynomialLiftNoInversePower
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HatNF.basicLiftAll_zero | exact GlobalTheory.HatNF.basicLiftAll_zero | (intros; apply GlobalTheory.HatNF.basicLiftAll_zero <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.basicOperators_polynomialLift_no_inversePower : BasicLiftAll (fun _ => 0) := by
  first | exact @GlobalTheory.HatNF.basicLiftAll_zero | exact GlobalTheory.HatNF.basicLiftAll_zero | (intros; apply GlobalTheory.HatNF.basicLiftAll_zero <;> assumption)
