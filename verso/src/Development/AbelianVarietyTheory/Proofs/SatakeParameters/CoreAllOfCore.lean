import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwOfContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsSDRAllOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsCsdCrysOfHoldsS
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoldsSGoodDROfCsd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedGoodOfSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineAllOfGoodStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusAllOfGoodStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusGoodOfSelfDualStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

/- English proof (translation)
Introduce `hI hC`. Take `⟨hex, hh⟩` from `hC`. Establish `exg : Ex .good` using `GlobalTheory.GalCut.ex_good_of_ex_csd GlobalTheory.automorphicFormsFiniteGL hex`. Establish `unrg : SphericalLevelCondition .good .unr` using `GlobalTheory.T.unramified_good_of_self_dual hI (hh .unr)`. Establish `crysg : SphericalLevelCondition .good .crys` using `holdsS_good_crys hI (hh .crys)`.

Use `⟨ex_all_of_good hI exg unrg, ?_⟩` and prove the remaining obligations. Introduce `c`. Consider the cases of `c with`. Consider the case `unr => exact GlobalTheory.UnrDescent.main hI unrg`. Consider the case `dR => exact holdsS_dR_all_of_good hI (holdsS_good_dR_of_csd hI (hh .dR))`.

Consider the case `crys => exact GlobalTheory.T.crystalline_all_of_good hI crysg`. Consider the case `phi => exact GlobalTheory.T.frobenius_all_of_good hI crysg (GlobalTheory.T.frobenius_good_of_self_dual hI (hh .crys) (hh .phi))`.
-/
theorem coreAll_of_core : Inputs → Core → CoreAll := by
  intro hI hC
  obtain ⟨hex, hh⟩ := hC
  have exg : Ex .good := GlobalTheory.GalCut.ex_good_of_ex_csd GlobalTheory.automorphicFormsFiniteGL hex
  have unrg : SphericalLevelCondition .good .unr := GlobalTheory.T.unramified_good_of_self_dual hI (hh .unr)
  have crysg : SphericalLevelCondition .good .crys := holdsS_good_crys hI (hh .crys)
  refine ⟨ex_all_of_good hI exg unrg, ?_⟩
  intro c
  cases c with
  | unr => exact GlobalTheory.UnrDescent.main hI unrg
  | dR => exact holdsS_dR_all_of_good hI (holdsS_good_dR_of_csd hI (hh .dR))
  | crys => exact GlobalTheory.T.crystalline_all_of_good hI crysg
  | phi => exact GlobalTheory.T.frobenius_all_of_good hI crysg (GlobalTheory.T.frobenius_good_of_self_dual hI (hh .crys) (hh .phi))

/- English proof (translation)
The claim follows from `coreAll_of_core`.
-/
example : Inputs → Core → CoreAll := coreAll_of_core

end GlobalTheory.RoadU

end
