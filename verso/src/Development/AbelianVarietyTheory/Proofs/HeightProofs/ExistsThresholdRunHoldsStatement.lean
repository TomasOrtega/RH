import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinalJoin.runHolds_of_parOK` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FExistsThresholdRunHolds.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.exists_threshold_run_holds : ∃ x₀ : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → RunHolds x₀ h hinj EX p := by
  first | exact @GlobalTheory.FinalJoin.runHolds_of_parOK | exact GlobalTheory.FinalJoin.runHolds_of_parOK | (intros; apply GlobalTheory.FinalJoin.runHolds_of_parOK <;> assumption)
