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
A detailed English derivation is pending.
-/
theorem sizeCont : SizeCont := GlobalTheory.CompanionTheory.SizeCont.sizeCont szFin
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degRight : DegRight := GlobalTheory.CompanionTheory.DegRightProof.degRight_of mulF mulI szFin finSupp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem redBasic : RedBasic := redBasic_of ratProper_holds sizeCont
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cutBox : CutBox := cutBox_of' degBasis degAdelic degBdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem redCell : RedCell := redCell_of sizeBasic degBdd degRat degRight torNorm_holds cutBox redBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cutRed : CutRed := cutRed_of degRat cellCover_holds cutBox redBasic redCell
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cntPair : CntPair := cntPair_of ratProper_holds thetaBasic_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtCount : WtCount := wtCount_of ratProper_holds cellSum cellCover_holds redBasic redCell GlobalTheory.CompanionTheory.LatticeSum.latSum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cutCount : CutCount := cutCount_of redBasic cutRed wtCount
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtDiag : WtDiag := wtDiag_of ratProper_holds cntBasic wtCount
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem vecsEx : VecsEx := GlobalTheory.CompanionTheory.DualVectorFamily.vecsEx_of ratProper_holds kerBasic kerLin cntBasic cntPair vecEx vecNorm vecInner ptEq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lBound : LBound := GlobalTheory.CompanionTheory.LBoundProof.lBound_of mahler_holds cutCount
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sFun_holds : SFun := sFun_of vecsEx lBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sBound_holds : F.SBound := sBound_of (sb_of sFun_holds)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bridge_holds : F.Bridge := bridge_of (GlobalTheory.CompanionTheory.PairDom.prodDom ratProper_holds)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opEx_holds : F.OpEx := opEx_of ratProper_holds opExA opAdj opMul
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernel_operator_exists_holds : E.SmoothSeminormGrowth := kernel_operator_exists_of opEx_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernel_diagonal_integrable_holds : E.KernelDiagonalIntegrable := kernel_diagonal_integrable_of ratProper_holds kerBasic kerLin opEx_holds wtDiag
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem growthJ_of_ell (h : D4.EllFormula2J) : GrowthJ := growthJ_of h sBound_holds bridge_holds domEx_holds

open MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL in
/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem nonempty_dom (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (a b : ℕ) : Nonempty (PositivityTheory.Rg.BcB.E.Dom E a b) := by
  obtain ⟨F₁, h₁⟩ := domEx_holds E a Measure.haar
  obtain ⟨F₂, h₂⟩ := domEx_holds E b Measure.haar
  obtain ⟨D, -⟩ := bridge_holds E a b Measure.haar Measure.haar F₁ F₂ h₁ h₂
  exact ⟨D⟩

end PositivityTheory.Rg.BcB.E1
