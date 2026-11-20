import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicRestrictionSubalgebraFrameDomainIsDom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResRdApply
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatPair.holAlg_isDomain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHolomorphicRestrictionSubalgebraFrameDomainIsDom.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  first | exact @GlobalTheory.FlatPair.holAlg_isDomain | exact GlobalTheory.FlatPair.holAlg_isDomain | (intros; apply GlobalTheory.FlatPair.holAlg_isDomain <;> assumption)
