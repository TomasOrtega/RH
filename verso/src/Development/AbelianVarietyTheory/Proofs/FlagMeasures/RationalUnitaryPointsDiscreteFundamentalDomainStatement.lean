import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RatDiscrete.rational_points` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRationalUnitaryPointsDiscreteFundamentalDomain.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain : ∀ I : AutInst, ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ Countable Γ ∧ (∀ C : Set I.GA, IsCompact C → (C ∩ I.GFset).Finite) ∧ ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → IsFundamentalDomain Γ fund (I.muA μf) := by
  first | exact @GlobalTheory.RatDiscrete.rational_points | exact GlobalTheory.RatDiscrete.rational_points | (intros; apply GlobalTheory.RatDiscrete.rational_points <;> assumption)
