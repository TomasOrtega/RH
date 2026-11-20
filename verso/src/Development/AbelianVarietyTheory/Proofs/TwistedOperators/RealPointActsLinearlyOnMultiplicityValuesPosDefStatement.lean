import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDef
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRealPointActsLinearlyOnMultiplicityValuesPosDef.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.realPoint_acts_linearly_on_multiplicity_values_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  first | exact @GlobalTheory.RealAct.real_acts | exact GlobalTheory.RealAct.real_acts | (intros; apply GlobalTheory.RealAct.real_acts <;> assumption)
