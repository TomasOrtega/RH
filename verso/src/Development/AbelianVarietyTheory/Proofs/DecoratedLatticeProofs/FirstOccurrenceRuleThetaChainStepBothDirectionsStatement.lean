import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StepRule.rulePar_step` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFirstOccurrenceRuleThetaChainStepBothDirections.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.firstOccurrenceRule_thetaChainStep_both_directions : ∀ (D : D7) (X : ProvA), Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → ∀ k : Fin D.R.m, ChainPar D k → ∀ τ, RulePar X (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) (expS D k τ) (expT D k τ) ∧ RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) := by
  first | exact @GlobalTheory.StepRule.rulePar_step | exact GlobalTheory.StepRule.rulePar_step | (intros; apply GlobalTheory.StepRule.rulePar_step <;> assumption)
