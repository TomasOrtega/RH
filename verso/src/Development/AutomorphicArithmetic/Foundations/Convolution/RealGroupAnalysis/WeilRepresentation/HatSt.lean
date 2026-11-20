import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatN
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.IntegralMulLeftAdele
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierEqAdelic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ThetaSq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.IntegralScale
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Sl2InductionUnipotentWeyl

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W`. Establish `hδ : D.δ ≠ 0`. Introduce `h0`. Establish `hθ : D.θ = 0`. Establish `h` using `D.sq`.

Rewrite `h` using `[h0, map_zero]`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.mp h`. Conclude with `D.b.ne_zero 1 (by rw [D.b1, hθ])`. Use `{ n := _root_.UpperTheory.ConvolutionTheory.R2.D.hatN F E D W m := _root_.UpperTheory.ConvolutionTheory.R2.D.hatM F E D W w := ?_ nE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatNE F E D W aE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatAE F E D W mem := fun φ => (_root_.Up …` and prove the remaining obligations. Introduce `φ v`.

Establish `h : (W.Om (wW F) φ).1 = ft4 D.δ φ.1` using `funext (W.Om_w φ)`. Rewrite using `[h]`. Conclude with `_root_.UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ v hδ`.
-/
theorem UpperTheory.ConvolutionTheory.R2.hatSt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), St.Hat W := by
  intro F E _ _ _ _ _ _ _ D W
  have hδ : D.δ ≠ 0 := by
    intro h0
    have hθ : D.θ = 0 := by
      have h := D.sq
      rw [h0, map_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    exact D.b.ne_zero 1 (by rw [D.b1, hθ])
  refine
    { n := _root_.UpperTheory.ConvolutionTheory.R2.D.hatN F E D W
      m := _root_.UpperTheory.ConvolutionTheory.R2.D.hatM F E D W
      w := ?_
      nE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatNE F E D W
      aE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatAE F E D W
      mem := fun φ => (_root_.UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1
      th := fun φ => (_root_.UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).2
      row := _root_.UpperTheory.ConvolutionTheory.R2.D.row F E D W }
  intro φ v
  have h : (W.Om (wW F) φ).1 = ft4 D.δ φ.1 := funext (W.Om_w φ)
  rw [h]
  exact _root_.UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ v hδ
