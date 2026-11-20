import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRing
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LitGood.litGoodO` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPadicIntegersFiniteExtGoodCoefficientRing.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing : LitGoodO := by
  first | exact @GlobalTheory.LitGood.litGoodO | exact GlobalTheory.LitGood.litGoodO | (intros; apply GlobalTheory.LitGood.litGoodO <;> assumption)
