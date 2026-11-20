import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationEqOfHeckeAgreementTwistLaws
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocSepTie.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLocalizationEqOfHeckeAgreementTwistLaws.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.localization_eq_of_heckeAgreement_twistLaws : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → GlobalTheory.RowTie.CharLaws D.nd D.naut → (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v → D.naut.locW i σ v = D.naut.locW i' σ v) → (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') → KillingConditions.LocalisationUniqueness D := by
  first | exact @GlobalTheory.LocSepTie.main | exact GlobalTheory.LocSepTie.main | (intros; apply GlobalTheory.LocSepTie.main <;> assumption)
