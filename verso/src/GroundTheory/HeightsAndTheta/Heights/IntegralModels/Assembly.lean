import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBundlesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PChartBundlesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PChartGlue
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PClearDenominators
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericGermInjective
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueBundles
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueModulesStar
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PInvOpenInside
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PInvOpenInsideRat
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PPrimeOpensCover
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PPullbackFaithful
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PRatLocalAffine
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundle
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundleNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHomInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadHomNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadIso
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadLocal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleLocal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ComapEqMaximalIdeal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.GenericImageEqGermImage
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsVectorBundleIffModel
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Imports
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.EquivAt
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IicEqRange
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.GlueBundlesSecondOfFirstAlt
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.NonemptyPullbackIsoIff
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.SpreadIsoModelIff
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.CpEqPrimeWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

/- English proof (translation)
The claim follows from `BlowUpChart.proof`.
-/
theorem BlowUpChart.full : BlowUpChart.Statement := BlowUpChart.proof

/- English proof (translation)
The claim follows from `ChartGlue.proof`.
-/
theorem ChartGlue.full : ChartGlue.Statement := ChartGlue.proof

/- English proof (translation)
The claim follows from `FiniteIntegralClosure.proof`.
-/
theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement := FiniteIntegralClosure.proof

/- English proof (translation)
The claim follows from `GenericGermInjective.proof`.
-/
theorem GenericGermInjective.full : GenericGermInjective.Statement := GenericGermInjective.proof

/- English proof (translation)
The claim follows from `GenericSectionsInj.proof`.
-/
theorem GenericSectionsInj.full : GenericSectionsInj.Statement := GenericSectionsInj.proof

/- English proof (translation)
The claim follows from `GlueModulesStar.proof`.
-/
theorem GlueModulesStar.full : GlueModulesStar.Statement := GlueModulesStar.proof

/- English proof (translation)
The claim follows from `HeightOneIntersection.proof`.
-/
theorem HeightOneIntersection.full : HeightOneIntersection.Statement := HeightOneIntersection.proof

/- English proof (translation)
The claim follows from `InvOpenInside.proof`.
-/
theorem InvOpenInside.full : InvOpenInside.Statement := InvOpenInside.proof

/- English proof (translation)
The claim follows from `InvOpenInsideRat.proof`.
-/
theorem InvOpenInsideRat.full : InvOpenInsideRat.Statement := InvOpenInsideRat.proof

/- English proof (translation)
The claim follows from `MertensUpper.proof`.
-/
theorem MertensUpper.full : MertensUpper.Statement := MertensUpper.proof

/- English proof (translation)
The claim follows from `PrimeOpensCover.proof`.
-/
theorem PrimeOpensCover.full : PrimeOpensCover.Statement := PrimeOpensCover.proof

/- English proof (translation)
The claim follows from `RatLocalAffine.proof`.
-/
theorem RatLocalAffine.full : RatLocalAffine.Statement := RatLocalAffine.proof

/- English proof (translation)
The claim follows from `SectionNef.proof`.
-/
theorem SectionNef.full : SectionNef.Statement := SectionNef.proof

/- English proof (translation)
The claim follows from `SectionNefGenerated.proof`.
-/
theorem SectionNefGenerated.full : SectionNefGenerated.Statement := SectionNefGenerated.proof

/- English proof (translation)
The claim follows from `TorsionFreeQuotientLength.proof`.
-/
theorem TorsionFreeQuotientLength.full : TorsionFreeQuotientLength.Statement := TorsionFreeQuotientLength.proof

/- English proof (translation)
The claim follows from `VectorBundleLocal.proof`.
-/
theorem VectorBundleLocal.full : VectorBundleLocal.Statement := VectorBundleLocal.proof

/- English proof (translation)
The claim follows from `VectorBundleRestrict.proof`.
-/
theorem VectorBundleRestrict.full : VectorBundleRestrict.Statement := VectorBundleRestrict.proof

/- English proof (translation)
The claim follows from `PullbackFaithful.proof`.
-/
theorem PullbackFaithful.full : PullbackFaithful.Statement.{0} := PullbackFaithful.proof

/- English proof (translation)
The claim follows from `KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full`.
-/
theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

/- English proof (translation)
The claim follows from `KrullAkizuki.proof KrullAkizukiQuotientLength.full`.
-/
theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

/- English proof (translation)
The claim follows from `DominatingDVR.proof KrullAkizuki.full BlowUpChart.full`.
-/
theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

/- English proof (translation)
The claim follows from `HeightOneSections.proof GenericGermInjective.full`.
-/
theorem HeightOneSections.full : HeightOneSections.Statement :=
  HeightOneSections.proof GenericGermInjective.full

/- English proof (translation)
The claim follows from `BundlesAgree.proof GenericGermInjective.full HeightOneSections.full`.
-/
theorem BundlesAgree.full : BundlesAgree.Statement :=
  BundlesAgree.proof GenericGermInjective.full HeightOneSections.full

/- English proof (translation)
The claim follows from `ChartBundlesAgree.proof HeightOneIntersection.full`.
-/
theorem ChartBundlesAgree.full : ChartBundlesAgree.Statement :=
  ChartBundlesAgree.proof HeightOneIntersection.full

/- English proof (translation)
The claim follows from `LatticesAgree.proof HeightOneIntersection.full`.
-/
theorem LatticesAgree.full : LatticesAgree.Statement :=
  LatticesAgree.proof HeightOneIntersection.full

/- English proof (translation)
The claim follows from `SumCp.proof MertensUpper.full`.
-/
theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

/- English proof (translation)
The claim follows from `SpreadHomInj.proof GenericSectionsInj.full PullbackFaithful.full`.
-/
theorem SpreadHomInj.full : SpreadHomInj.Statement :=
  SpreadHomInj.proof GenericSectionsInj.full PullbackFaithful.full

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.normalization_of_scheme (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.scheme_of_alg (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteI …`.
-/
theorem FiniteNormalization.full : FiniteNormalization.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.normalization_of_scheme
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.scheme_of_alg
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.alg_iff.mp FiniteIntegralClosure.full))

/- English proof (translation)
The claim follows from `ClearDenominators.proof hPB RatLocalAffine.full`.
-/
theorem ClearDenominators.of_open (hPB : PullbackBasis.Statement.{0}) :
    ClearDenominators.Statement :=
  ClearDenominators.proof hPB RatLocalAffine.full

/- English proof (translation)
The claim follows from `SpreadLocal.proof hFB hBI`.
-/
theorem SpreadLocal.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) : SpreadLocal.Statement :=
  SpreadLocal.proof hFB hBI

/- English proof (translation)
The claim follows from `SpreadBundleNbhd.proof (SpreadLocal.of_open hFB hBI) hSS`.
-/
theorem SpreadBundleNbhd.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement) :
    SpreadBundleNbhd.Statement :=
  SpreadBundleNbhd.proof (SpreadLocal.of_open hFB hBI) hSS

/- English proof (translation)
The claim follows from `SpreadBundle.proof (SpreadBundleNbhd.of_open hFB hBI hSS) InvOpenInside.full`.
-/
theorem SpreadBundle.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement) : SpreadBundle.Statement :=
  SpreadBundle.proof (SpreadBundleNbhd.of_open hFB hBI hSS) InvOpenInside.full

/- English proof (translation)
The claim follows from `SpreadHomNbhd.proof hDH hGP hHS`.
-/
theorem SpreadHomNbhd.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadHomNbhd.Statement :=
  SpreadHomNbhd.proof hDH hGP hHS

/- English proof (translation)
The claim follows from `SpreadHom.proof (SpreadHomNbhd.of_open hDH hGP hHS) InvOpenInsideRat.full`.
-/
theorem SpreadHom.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadHom.Statement :=
  SpreadHom.proof (SpreadHomNbhd.of_open hDH hGP hHS) InvOpenInsideRat.full

/- English proof (translation)
The claim follows from `SpreadIso.proof (SpreadHom.of_open hDH hGP hHS) SpreadHomInj.full`.
-/
theorem SpreadIso.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadIso.Statement :=
  SpreadIso.proof (SpreadHom.of_open hDH hGP hHS) SpreadHomInj.full

/- English proof (translation)
The claim follows from `GlueBundles.proof (SpreadBundle.of_open hFB hBI hSS) (SpreadIso.of_open hDH hGP hHS) PrimeOpensCover.full GlueModulesStar.full VectorBundleRestrict.full VectorBundleLocal.full`.
-/
theorem GlueBundles.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement)
    (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : GlueBundles.Statement :=
  GlueBundles.proof (SpreadBundle.of_open hFB hBI hSS) (SpreadIso.of_open hDH hGP hHS)
    PrimeOpensCover.full GlueModulesStar.full VectorBundleRestrict.full VectorBundleLocal.full

end GroundTheory.Heights₂.Heights.Model

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

/- English proof (translation)
The claim follows from `BlowUpChart.equiv.mp GroundTheory.Heights₂.Heights.Model.BlowUpChart.full`.
-/
theorem BlowUpChart.full : BlowUpChart.Statement :=
  BlowUpChart.equiv.mp GroundTheory.Heights₂.Heights.Model.BlowUpChart.full

/- English proof (translation)
The claim follows from `BundlesAgree.equiv.mp GroundTheory.Heights₂.Heights.Model.BundlesAgree.full`.
-/
theorem BundlesAgree.full : BundlesAgree.Statement :=
  BundlesAgree.equiv.mp GroundTheory.Heights₂.Heights.Model.BundlesAgree.full

/- English proof (translation)
The claim follows from `HeightOneIntersection.equiv.mp GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.full`.
-/
theorem HeightOneIntersection.full : HeightOneIntersection.Statement :=
  HeightOneIntersection.equiv.mp GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.full

/- English proof (translation)
The claim follows from `KrullAkizuki.equiv.mp GroundTheory.Heights₂.Heights.Model.KrullAkizuki.full`.
-/
theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.equiv.mp GroundTheory.Heights₂.Heights.Model.KrullAkizuki.full

/- English proof (translation)
The claim follows from `LatticesAgree.equiv.mp GroundTheory.Heights₂.Heights.Model.LatticesAgree.full`.
-/
theorem LatticesAgree.full : LatticesAgree.Statement :=
  LatticesAgree.equiv.mp GroundTheory.Heights₂.Heights.Model.LatticesAgree.full

/- English proof (translation)
The claim follows from `MertensUpper.equiv.mp GroundTheory.Heights₂.Heights.Model.MertensUpper.full`.
-/
theorem MertensUpper.full : MertensUpper.Statement :=
  MertensUpper.equiv.mp GroundTheory.Heights₂.Heights.Model.MertensUpper.full

/- English proof (translation)
The claim follows from `SumCp.equiv.mp GroundTheory.Heights₂.Heights.Model.SumCp.full`.
-/
theorem SumCp.full : SumCp.Statement :=
  SumCp.equiv.mp GroundTheory.Heights₂.Heights.Model.SumCp.full

/- English proof (translation)
The claim follows from `SectionNef.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.SectionNef.full, GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.full⟩`.
-/
theorem SectionNef.full : SectionNef.Statement :=
  SectionNef.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.SectionNef.full,
    GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.full⟩

/- English proof (translation)
The claim follows from `FiniteIntegralClosure.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full, GroundTheory.Heights₂.Heights.Model.FiniteNormalization.full⟩`.
-/
theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement :=
  FiniteIntegralClosure.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full,
    GroundTheory.Heights₂.Heights.Model.FiniteNormalization.full⟩

/- English proof (translation)
The claim follows from `DominatingDVR.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.DominatingDVR.full, hS⟩`.
-/
theorem DominatingDVR.of_open (hS : GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.Statement) :
    DominatingDVR.Statement :=
  DominatingDVR.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.DominatingDVR.full, hS⟩

/- English proof (translation)
The claim follows from `ClearDenominators.equiv.mp (GroundTheory.Heights₂.Heights.Model.ClearDenominators.of_open hPB)`.
-/
theorem ClearDenominators.of_open
    (hPB : GroundTheory.Heights₂.Heights.Model.PullbackBasis.Statement.{0}) :
    ClearDenominators.Statement :=
  ClearDenominators.equiv.mp (GroundTheory.Heights₂.Heights.Model.ClearDenominators.of_open hPB)

/- English proof (translation)
The claim follows from `SpreadBundle.equiv.mp (GroundTheory.Heights₂.Heights.Model.SpreadBundle.of_open hFB hBI hSS)`.
-/
theorem SpreadBundle.of_open (hFB : GroundTheory.Heights₂.Heights.Model.FreeSheafBasis.Statement.{0})
    (hBI : GroundTheory.Heights₂.Heights.Model.BasisIsoFree.Statement.{0})
    (hSS : GroundTheory.Heights₂.Heights.Model.SpreadStep.Statement) : SpreadBundle.Statement :=
  SpreadBundle.equiv.mp (GroundTheory.Heights₂.Heights.Model.SpreadBundle.of_open hFB hBI hSS)

/- English proof (translation)
The claim follows from `SpreadIso.equiv.mp (GroundTheory.Heights₂.Heights.Model.SpreadIso.of_open hDH hGP hHS)`.
-/
theorem SpreadIso.of_open (hDH : GroundTheory.Heights₂.Heights.Model.DescendHom.Statement)
    (hGP : GroundTheory.Heights₂.Heights.Model.GenericPullInj.Statement)
    (hHS : GroundTheory.Heights₂.Heights.Model.SpreadHomSections.Statement) : SpreadIso.Statement :=
  SpreadIso.equiv.mp (GroundTheory.Heights₂.Heights.Model.SpreadIso.of_open hDH hGP hHS)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
