import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.ZeroExp
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.AbsCount2
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LogAsym
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.ClassChar2
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Decomp
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SysEx
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.CoverEx
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.UnitOfPow
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPow
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.FibreCG
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.TwoParts
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftSum
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftPow
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.PartBOfDecomposition
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

open PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

/- English proof (translation)
The claim follows from `count (absCount2 bcSum_holds zeroExp logAsym) sysEx (coverEx decomp)`.
-/
theorem count_holds : Count := count (absCount2 bcSum_holds zeroExp logAsym) sysEx (coverEx decomp)

/- English proof (translation)
The claim follows from `normCharPow count_holds`.
-/
theorem normCharPow_holds : NormCharPow := normCharPow count_holds

/- English proof (translation)
The claim follows from `fibreCG classChar2 count_holds normCharPow_holds`.
-/
theorem fibreCG_holds : FibreCG := fibreCG classChar2 count_holds normCharPow_holds

/- English proof (translation)
The claim follows from `fibre fibreCG_holds`.
-/
theorem fibre_holds : Fibre := fibre fibreCG_holds

/- English proof (translation)
The claim follows from `twoParts classChar2 count_holds normCharPow_holds`.
-/
theorem twoParts_holds : TwoParts := twoParts classChar2 count_holds normCharPow_holds

/- English proof (translation)
Introduce `E _ _ _ n P ι _ m Ps hn hm hι h`. Take `⟨s, -⟩` from `PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E Unit ι (fun _ => n) m (fun _ => P) Ps (fun _ => hn) hm (h.mono fun w ⟨C, B, h1, h2, h3⟩ => ⟨fun _ => C, B, fun _ => h1, h2, by simp [h3]⟩)`. Use `Fintype.card_congr s` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem partA_holds : PartA := by
  intro E _ _ _ n P ι _ m Ps hn hm hι h
  obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E Unit ι (fun _ => n) m (fun _ => P) Ps (fun _ => hn) hm
    (h.mono fun w ⟨C, B, h1, h2, h3⟩ => ⟨fun _ => C, B, fun _ => h1, h2, by simp [h3]⟩)
  have := Fintype.card_congr s
  simp at this
  omega

end UpperTheory.ConvolutionTheory.R
