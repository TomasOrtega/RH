import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDerivationExtendLocalizationAtPrime.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_derivation_extend_localization_atPrime : ∀ (F A R : Type) [CommRing F] [CommRing A] [CommRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (D : Derivation F A R), ∃ D' : Derivation F R R, ∀ a, D' (algebraMap A R a) = D a := by
  first | exact @GlobalTheory.derivation_extend_localization_atPrime | exact GlobalTheory.derivation_extend_localization_atPrime | (intros; apply GlobalTheory.derivation_extend_localization_atPrime <;> assumption)
