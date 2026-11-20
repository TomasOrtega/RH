import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `K _ _ _ n hn P P' h`. Take `⟨s, hs⟩` from `PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity K Unit Unit (fun _ => n) (fun _ => n) (fun _ => CG.mk P) (fun _ => CG.mk P') (fun _ => hn) (fun _ => hn) (h.mono fun w ⟨B, h1, h2⟩ => ⟨fun _ => B, fun _ => B, fun _ => h1, fun _ => h2, rfl⟩)`. Establish `e : (CG.mk P : CG K n) = CG.mk P'` using `eq_of_heq (Sigma.mk.inj (hs ())).2`. Conclude with `(UpperTheory.ConvolutionTheory.Dp.isoEq K n P P').1 (Quotient.exact e)`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.smoEq :
    UpperTheory.ConvolutionTheory.Sph.SmoEq := by
  intro K _ _ _ n hn P P' h
  obtain ⟨s, hs⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity K Unit Unit (fun _ => n) (fun _ => n)
    (fun _ => CG.mk P) (fun _ => CG.mk P') (fun _ => hn) (fun _ => hn)
    (h.mono fun w ⟨B, h1, h2⟩ => ⟨fun _ => B, fun _ => B, fun _ => h1, fun _ => h2, rfl⟩)
  have e : (CG.mk P : CG K n) = CG.mk P' := eq_of_heq (Sigma.mk.inj (hs ())).2
  exact (UpperTheory.ConvolutionTheory.Dp.isoEq K n P P').1 (Quotient.exact e)
