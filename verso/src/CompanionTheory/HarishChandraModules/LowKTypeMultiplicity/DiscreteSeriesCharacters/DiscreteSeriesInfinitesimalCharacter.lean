import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CarImpFrel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommuteOfUnitaryConjugate
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreAnnApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemFiltOfWords
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KummerLiftedCocycleImageEqPicardClass
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordMonomial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlkBijective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZetaDegZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BlkStrictMono
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WlemOfGfacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IndOfNot
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumInsertErase
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CardOther
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KhwExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InnerEqZeroOfWeight
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HwMapOfLowSpan
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsCocycleOfMapToDegreeOneTerm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AlgCoreSubOfAlgCore
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MulMemUJset
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExt
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GlRelOfBracket
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ImportsAlt
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.Spread
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemUJsetOfMemKset
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KExp
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExpMemUJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExpMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NotCdomAddRoot
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KsetSubsetUjset
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CobApplyOfDeg
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll

namespace CompanionTheory.D.DSIC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hCAR : CAR := GlobalTheory.CompanionTheory.ChainCAR.car
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hFRel : FRel := GlobalTheory.CompanionTheory.DSICFRel.car_imp_frel hCAR
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hBdFacts : BdFacts := GlobalTheory.CompanionTheory.KoszulBd.bdFacts hCAR
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hGFacts : GFacts := GlobalTheory.CompanionTheory.GopEntries.gFacts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hKoszul : Koszul := GlobalTheory.CompanionTheory.DSICKoszul.koszul hCAR
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hVerma : Verma := GlobalTheory.CompanionTheory.DSVerma.verma
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hCover : Cover := GlobalTheory.CompanionTheory.DSCover.cover hKoszul hVerma
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hCO0 : CapelliDeterminantBlockProduct := GlobalTheory.CompanionTheory.CapelliBlocks.co0
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hCO : CO := GlobalTheory.CompanionTheory.CasselmanOsborne.co_of hBdFacts hGFacts hCover hCO0
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hZetaHW : ZetaHW := GlobalTheory.CompanionTheory.ZetaHighest.zetaHW
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hWLem : WLem := GlobalTheory.CompanionTheory.DSICWLem.wlem_of_gfacts hGFacts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hNormLt : NormLt := GlobalTheory.CompanionTheory.DSNormLt.normLt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hAdj : Adj := GlobalTheory.CompanionTheory.DSChainAdj.adj
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hGamDom : GamDom := GlobalTheory.CompanionTheory.GamDomProof.gamDom
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hKHWExists : KHWExists := GlobalTheory.CompanionTheory.KHighestExists.khwExists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hLowSpan : LowSpan := GlobalTheory.CompanionTheory.KLowSpan.lowSpan_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hHWMap : HWMap := GlobalTheory.CompanionTheory.DSICHWMap.hwMap_of_lowSpan hLowSpan
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hPRV : PRV := GlobalTheory.CompanionTheory.ChainHighest.aux₃ hFRel hGFacts hGamDom hKHWExists hHWMap
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hAlgCore : AlgCore := algCore_of hFRel hBdFacts hCO hZetaHW hWLem hNormLt hAdj hPRV
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hAlgCoreSub : AlgCoreSub := GlobalTheory.CompanionTheory.DSCoreSub.algCoreSub_of_algCore hAlgCore
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hSmLin : SmLin := GlobalTheory.CompanionTheory.DSSmLin.smLin
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hSmBracket : SmBracket := GlobalTheory.CompanionTheory.SmBracket.smBracket_of hSmLin
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hSmMod : SmMod := GlobalTheory.CompanionTheory.SmoothModule.smMod hSmLin hSmBracket
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hActQ : ActQ := GlobalTheory.CompanionTheory.DSCapelliAction.actQ
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hSpread : Spread := capelli_spread
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hKFinStab : KFinStab := GlobalTheory.CompanionTheory.KFinStab.kFinStab
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hKExp : KExp := GlobalTheory.CompanionTheory.DSICKExp.kExp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hStabLink : StabLink := GlobalTheory.CompanionTheory.DSStabLink.stabLink hKExp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hWtLink : WtLink := GlobalTheory.CompanionTheory.WtLinkPf.wtLink
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hHWofType : HWofType := GlobalTheory.CompanionTheory.DSHighestOfKType.hwOfType hStabLink hWtLink
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hTypeOfHW : TypeOfHW := GlobalTheory.CompanionTheory.DSKType.typeOfHW hLowSpan hStabLink hWtLink

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discrete_series_infinitesimal_character : PI.DSInfCharCap.DSInfCharCap :=
  dsInfCharCap_of hAlgCoreSub hSmMod hActQ hSpread CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs hKFinStab hStabLink
    hHWofType hTypeOfHW

end CompanionTheory.D.DSIC
