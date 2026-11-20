import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLocalBoundTableAllPrimesConditionTwoThree.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.smallPrimeLengthBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  first | exact @GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree | exact GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree | (intros; apply GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree <;> assumption)
