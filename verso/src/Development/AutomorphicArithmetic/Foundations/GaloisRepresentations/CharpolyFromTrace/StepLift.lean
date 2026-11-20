import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CbcCOfCbcc
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnderStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPowStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

/- English proof (translation)
Introduce `hC hN hP hW K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l a _ ha π χ hs A v hv hτ hsat`. Take `⟨hreg, hpol, -⟩` from `hs`. Establish `hK : IsTotallyComplex K` using `inferInstance`. Establish `hM : IsTotallyComplex M` using `inferInstance`. Break down `(hC K M hp hK a ha).1 (.cx π) with ⟨η, hη, hi⟩ | ⟨Q, hw, hinf, hsplit⟩` into its components or cases.

It suffices to derive a contradiction. Take `⟨B, hB⟩` from `hsat`. Use `hN K M Ω hp A v hv hτ a ha (CG.mk π) B hB η hη ?_` and prove the remaining obligations. Rewrite using `[CG.twist_mk]`. Conclude with `Quotient.sound hi`.

Consider the cases of `Q with`. Consider the case `re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex M inferInstance hM).elim`. Consider the case `cx P`. Establish `hw' : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat` using `hw`. Take `⟨⟨χ', hχ'⟩, hq⟩` from `hP K M a ha π P χ hpol hw'`.

Use `⟨P, χ', hw, hsplit, ⟨?_, hχ', trivial⟩, hq, fun ι r hr => hW K M Ω l ι a π P hw' r hr⟩` and prove the remaining obligations. Use `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap K M))`. Establish `h2 : P.HasInfChar τ ((CG.mk π).infChar (τ.comp (algebraMap K M)))` using `hinf τ _ h1`. Establish `h3 : (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M))` using `CG.HasInfChar.infChar_eq h2`.

Rewrite using `[h3]`. Conclude with `hreg _`.
-/
theorem UpperTheory.Gal.NearKilling.stepLift :
    UpperTheory.V.Z.Bc.CBCc → UpperTheory.Gal.UnramifiedFromSplittingCriterion.NoSelfTwist → PolBC → WeakRes → StepLift := by
  intro hC hN hP hW K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l a _ ha π χ hs A v hv hτ hsat
  obtain ⟨hreg, hpol, -⟩ := hs
  have hK : IsTotallyComplex K := inferInstance
  have hM : IsTotallyComplex M := inferInstance
  rcases (hC K M hp hK a ha).1 (.cx π) with ⟨η, hη, hi⟩ | ⟨Q, hw, hinf, hsplit⟩
  · exfalso
    obtain ⟨B, hB⟩ := hsat
    refine hN K M Ω hp A v hv hτ a ha (CG.mk π) B hB η hη ?_
    rw [CG.twist_mk]
    exact Quotient.sound hi
  · cases Q with
    | re Q => exact (PositivityTheory.Pf1.CLGD.K.LKW.not_real_complex M inferInstance hM).elim
    | cx P =>
      have hw' : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := hw
      obtain ⟨⟨χ', hχ'⟩, hq⟩ := hP K M a ha π P χ hpol hw'
      refine ⟨P, χ', hw, hsplit, ⟨?_, hχ', trivial⟩, hq, fun ι r hr => hW K M Ω l ι a π P hw' r hr⟩
      refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
      have h1 := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap K M))
      have h2 : P.HasInfChar τ ((CG.mk π).infChar (τ.comp (algebraMap K M))) := hinf τ _ h1
      have h3 : (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M)) :=
        CG.HasInfChar.infChar_eq h2
      rw [h3]
      exact hreg _
