import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeCommuteOfTwistSeriesSideData
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSplitPlaceHeckeCommuteOfTwistSeriesSideData.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.splitPlaceHeckeCommute_of_twistSeriesSideData : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), HkComm D := by
  first | exact @GlobalTheory.SupLaw.hkComm_of_ties | exact GlobalTheory.SupLaw.hkComm_of_ties | (intros; apply GlobalTheory.SupLaw.hkComm_of_ties <;> assumption)
