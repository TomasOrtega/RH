import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HeightCounting.FormsStep.eIdem_all | exact GlobalTheory.HeightCounting.FormsStep.eIdem_all | (intros; apply GlobalTheory.HeightCounting.FormsStep.eIdem_all <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.isCentralGroupAlgebraIdempotent_universal : ∀ D : D7, EIdem D := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.eIdem_all | exact GlobalTheory.HeightCounting.FormsStep.eIdem_all | (intros; apply GlobalTheory.HeightCounting.FormsStep.eIdem_all <;> assumption)
