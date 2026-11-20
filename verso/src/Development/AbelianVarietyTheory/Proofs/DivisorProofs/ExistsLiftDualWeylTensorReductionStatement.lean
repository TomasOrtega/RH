import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftDualWeylTensorReduction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLiftDualWeylTensorReduction.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.exists_lift_dualWeylTensorReduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange → ∀ P ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (mu τ)), ∃ y : NablaT O N mu, redT O N mu ϖ y = P := by
  first | exact @GlobalTheory.HighWtEmb.nabK_lift | exact GlobalTheory.HighWtEmb.nabK_lift | (intros; apply GlobalTheory.HighWtEmb.nabK_lift <;> assumption)
