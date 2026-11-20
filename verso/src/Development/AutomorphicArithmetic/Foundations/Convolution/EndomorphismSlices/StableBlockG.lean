import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.REndoOf
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.BadFinite
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RStable
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PeakRun
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.GenSt
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RepAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ArEx
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LvEx
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowRep
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbEll
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowNorm
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RealUnivNe

open UpperTheory.V.Z.Tf.GlobalTraceComparison PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.Zero.ConvolutionTheory.EB

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem specP (P : Pred) (h : CuspReadP P) : Spec P := rSpec_of peakRun genSt ptOk hkMul repAlg positionTest P (rRead P h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem endoP (P : Pred) (h : CuspReadP P) : EndoP P :=
  rEndo_of arEx lvEx powRep cmbTest cmbEll repAlg powNorm P (specP P h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stableP (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) (P : Pred) (h : CuspReadP P) :
    StableP P := rStable h2 h3 h5 (cmbPi h1 h4) P (specP P h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem endoBlock (h : CuspRead) : EndoBlock := endo_of _ (endoP _ (cuspReadP_true h))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem endoBlockG (h : CuspReadI) : EndoBlockG := endoG_of (endoP _ (cuspReadP_inf h))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stableBlock (h : CuspRead) (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) : StableBlock :=
  stable_of _ (stableP h1 h2 h3 h4 h5 _ (cuspReadP_true h))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stableBlockG (h : CuspReadI) (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) : StableBlockG :=
  stableG_of (stableP h1 h2 h3 h4 h5 _ (cuspReadP_inf h))

end UpperTheory.Zero.ConvolutionTheory.EB
