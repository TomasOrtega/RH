import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Corank
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DCRelEquiv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermCarrierStable
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdCellInS
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSClassConst
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSRelevant
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PairCorankPos
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalEquivGen
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalarEquivalenceHermitianSpace
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaModX
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalRelRepFree
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalarPairDr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGCardUni
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGConvScalar
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGGenRatio
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMatBound
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMirBound
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WhitFunctDual
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CdHaarScale
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.BetaIndep
import Formalism.PadicSubsetSums.StableGradedCounts.MemBesselSetZeroIffUpperTriangular

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed

section Terms

variable (D : D7) (u u' : D.what₂.Word)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TermEqIff_holds : Formalism.L2.SG.TermDef.TermEqIff D u u' := term_eq_iff_relation D u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TermStable_holds : Formalism.L2.SG.TermDef.TermStable D u u' := term_carrier_stable D u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TermFun_holds : Formalism.L2.SG.TermDef.TermFun D u u' := term_function_const D u u'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TermInSFun_holds : Formalism.L2.SG.FourParts.TermInSFun D u u' := in_s_class_constant D u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TermInSRel_holds : Formalism.L2.SG.FourParts.TermInSRel D u u' := in_s_relevant D u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TermIdIffInS_holds : Formalism.L2.SG.FourParts.TermIdIffInS D u u' := term_id_iff_in_s D u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FourParts_holds : Formalism.L2.SG.FourParts.FourParts D u u' := Formalism.L2.SG.FourParts.fourParts_of_termFun (D := D) (TermFun_holds D u u')

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CorankPos_holds : Formalism.L2.SG.Corank.CorankPos D u u' := Formalism.L2.SG.Corank.corankPos_of_G (D := D) pair_corank_pos u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ScalarEquiv_holds : Formalism.L2.SG.Corank.ScalarEquiv D u u' := Formalism.L2.SG.Corank.scalarEquiv_of_G (D := D) scalar_equiv_general u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ScalarRepFree_holds : Formalism.L2.SG.Corank.ScalarRepFree D u u' := scalar_rep_free D u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ScalarEquivT_holds : Formalism.L2.SG.Corank.ScalarEquivT D u u' := Formalism.L2.SG.Corank.scalarEquivT_of (TermEqIff_holds D u u') (ScalarEquiv_holds D u u')
    (ScalarRepFree_holds D u u')
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BetaL_holds : Formalism.L2.SG.Corank.BetaL D u u' := beta_mod_iota_surjective D u u'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BetaFree_holds : Formalism.L2.SG.Corank.BetaFree D u u' := scalPairs_betaFree D u u'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem ScalarDr_holds : Formalism.L2.SG.Corank.ScalarDr D u u' := by
  intro F0 what₂ hrows p hp
  exact scalar_pair_dr D u u' F0 what₂ hrows p.lam p.mem p.fst p.snd p.G_fst p.G_snd p.beta p.isPair
    hp.1 hp.2

end Terms

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CorankPosG_holds : Formalism.L2.SG.Corank.CorankPosG := pair_corank_pos
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ScalarEquivG_holds : Formalism.L2.SG.Corank.ScalarEquivG := scalar_equiv_general

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GelfandGraevMultOne_holds : Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne := whittaker_functional_dual Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gelfand_graev_multiplicity_one
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CardUni_holds : Formalism.L2.SG.GGMirabolic.CardUni := PI.GGCardUniWork.cardUni
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MirabolicBound_holds : Formalism.L2.SG.GGMirabolic.MirabolicBound := mirabolic_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConvScalarOfLit_holds : Formalism.L2.SG.GGMirabolic.ConvScalarOfLit := convolution_scalar
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenericRatioOfBound_holds : Formalism.L2.SG.GGMirabolic.GenericRatioOfBound := PI.GGRatio.genericRatioOfBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GGMatrixBoundOfLit_holds : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit := gg_matrix_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConvScalar_holds : Formalism.L2.SG.GGMirabolic.ConvScalar :=
  ConvScalarOfLit_holds GelfandGraevMultOne_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenericRatio_holds : Formalism.L2.SG.GGMirabolic.GenericRatio :=
  GenericRatioOfBound_holds MirabolicBound_holds CardUni_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GGMatrixBound_holds : Formalism.L2.SG.GGMirabolic.GGMatrixBound :=
  GGMatrixBoundOfLit_holds GelfandGraevMultOne_holds MirabolicBound_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TermsGGBound_holds : Formalism.L2.SG.GGMirabolic.TermsGGBound :=
  Formalism.L2.SG.GGMirabolic.termsGGBound_of_matrix GGMatrixBound_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CdScaleExists_holds (D : D7) : Formalism.L2.SG.PairVal.CdScaleExists D := cd_haar_scaling D.cd

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsSplitRow_holds (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) :
    Formalism.L2.SG.Saturated.IsSplitRow D F0 Λ := split_row_iso D u F0 Λ hΛ

end Formalism.L2.SG.Closed
