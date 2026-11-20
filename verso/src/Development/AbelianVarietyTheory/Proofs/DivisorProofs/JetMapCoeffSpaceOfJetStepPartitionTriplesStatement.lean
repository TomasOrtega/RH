import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMapCoeffSpaceOfJetStepPartitionTriples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ColNorms.jetInVV_of_stepWeights` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJetMapCoeffSpaceOfJetStepPartitionTriples.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.jetMap_coeffSpace_of_jetStepPartitionTriples : ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (a b : ℕ), a < b → ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ) := by
  first | exact @GlobalTheory.ColNorms.jetInVV_of_stepWeights | exact GlobalTheory.ColNorms.jetInVV_of_stepWeights | (intros; apply GlobalTheory.ColNorms.jetInVV_of_stepWeights <;> assumption)
