import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnder
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjUnder.cPl_under` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FUnderConjugatePlaceEqConjugatePlaceUnder.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.under_conjugatePlace_eq_conjugatePlace_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.ConjUnder.cPl_under | exact GlobalTheory.ConjUnder.cPl_under | (intros; apply GlobalTheory.ConjUnder.cPl_under <;> assumption)
