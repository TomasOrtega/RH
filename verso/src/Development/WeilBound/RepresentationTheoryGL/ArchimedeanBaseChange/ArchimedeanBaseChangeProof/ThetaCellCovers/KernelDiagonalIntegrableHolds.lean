import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.MahlerFinal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.CutCountOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLogSizeM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFundamentalDomainRangeProdMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMulSqLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulLeSqAddSq

namespace PositivityTheory.Rg.BcB.E1

open D1

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.SizeCont.sizeCont szFin`.
-/
theorem sizeCont : SizeCont := GlobalTheory.CompanionTheory.SizeCont.sizeCont szFin
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.DegRightProof.degRight_of mulF mulI szFin finSupp`.
-/
theorem degRight : DegRight := GlobalTheory.CompanionTheory.DegRightProof.degRight_of mulF mulI szFin finSupp
/- English proof (translation)
The claim follows from `redBasic_of ratProper_holds sizeCont`.
-/
theorem redBasic : RedBasic := redBasic_of ratProper_holds sizeCont
/- English proof (translation)
The claim follows from `cutBox_of' degBasis degAdelic degBdd`.
-/
theorem cutBox : CutBox := cutBox_of' degBasis degAdelic degBdd
/- English proof (translation)
The claim follows from `redCell_of sizeBasic degBdd degRat degRight torNorm_holds cutBox redBasic`.
-/
theorem redCell : RedCell := redCell_of sizeBasic degBdd degRat degRight torNorm_holds cutBox redBasic
/- English proof (translation)
The claim follows from `cutRed_of degRat cellCover_holds cutBox redBasic redCell`.
-/
theorem cutRed : CutRed := cutRed_of degRat cellCover_holds cutBox redBasic redCell
/- English proof (translation)
The claim follows from `cntPair_of ratProper_holds thetaBasic_holds`.
-/
theorem cntPair : CntPair := cntPair_of ratProper_holds thetaBasic_holds
/- English proof (translation)
The claim follows from `wtCount_of ratProper_holds cellSum cellCover_holds redBasic redCell GlobalTheory.CompanionTheory.LatticeSum.latSum`.
-/
theorem wtCount : WtCount := wtCount_of ratProper_holds cellSum cellCover_holds redBasic redCell GlobalTheory.CompanionTheory.LatticeSum.latSum
/- English proof (translation)
The claim follows from `cutCount_of redBasic cutRed wtCount`.
-/
theorem cutCount : CutCount := cutCount_of redBasic cutRed wtCount
/- English proof (translation)
The claim follows from `wtDiag_of ratProper_holds cntBasic wtCount`.
-/
theorem wtDiag : WtDiag := wtDiag_of ratProper_holds cntBasic wtCount
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.DualVectorFamily.vecsEx_of ratProper_holds kerBasic kerLin cntBasic cntPair vecEx vecNorm vecInner ptEq`.
-/
theorem vecsEx : VecsEx := GlobalTheory.CompanionTheory.DualVectorFamily.vecsEx_of ratProper_holds kerBasic kerLin cntBasic cntPair vecEx vecNorm vecInner ptEq
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.LBoundProof.lBound_of mahler_holds cutCount`.
-/
theorem lBound : LBound := GlobalTheory.CompanionTheory.LBoundProof.lBound_of mahler_holds cutCount
/- English proof (translation)
The claim follows from `sFun_of vecsEx lBound`.
-/
theorem sFun_holds : SFun := sFun_of vecsEx lBound
/- English proof (translation)
The claim follows from `sBound_of (sb_of sFun_holds)`.
-/
theorem sBound_holds : F.SBound := sBound_of (sb_of sFun_holds)
/- English proof (translation)
The claim follows from `bridge_of (GlobalTheory.CompanionTheory.PairDom.prodDom ratProper_holds)`.
-/
theorem bridge_holds : F.Bridge := bridge_of (GlobalTheory.CompanionTheory.PairDom.prodDom ratProper_holds)
/- English proof (translation)
The claim follows from `opEx_of ratProper_holds opExA opAdj opMul`.
-/
theorem opEx_holds : F.OpEx := opEx_of ratProper_holds opExA opAdj opMul
/- English proof (translation)
The claim follows from `kernel_operator_exists_of opEx_holds`.
-/
theorem kernel_operator_exists_holds : E.SmoothSeminormGrowth := kernel_operator_exists_of opEx_holds
/- English proof (translation)
The claim follows from `kernel_diagonal_integrable_of ratProper_holds kerBasic kerLin opEx_holds wtDiag`.
-/
theorem kernel_diagonal_integrable_holds : E.KernelDiagonalIntegrable := kernel_diagonal_integrable_of ratProper_holds kerBasic kerLin opEx_holds wtDiag
/- English proof (translation)
The claim follows from `growthJ_of h sBound_holds bridge_holds domEx_holds`.
-/
theorem growthJ_of_ell (h : D4.EllFormula2J) : GrowthJ := growthJ_of h sBound_holds bridge_holds domEx_holds

open MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL in
/- English proof (translation)
Take `⟨F₁, h₁⟩` from `domEx_holds E a Measure.haar`. Take `⟨F₂, h₂⟩` from `domEx_holds E b Measure.haar`. Take `⟨D, -⟩` from `bridge_holds E a b Measure.haar Measure.haar F₁ F₂ h₁ h₂`. Conclude with `⟨D⟩`.
-/
theorem nonempty_dom (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (a b : ℕ) : Nonempty (PositivityTheory.Rg.BcB.E.Dom E a b) := by
  obtain ⟨F₁, h₁⟩ := domEx_holds E a Measure.haar
  obtain ⟨F₂, h₂⟩ := domEx_holds E b Measure.haar
  obtain ⟨D, -⟩ := bridge_holds E a b Measure.haar Measure.haar F₁ F₂ h₁ h₂
  exact ⟨D⟩

end PositivityTheory.Rg.BcB.E1
