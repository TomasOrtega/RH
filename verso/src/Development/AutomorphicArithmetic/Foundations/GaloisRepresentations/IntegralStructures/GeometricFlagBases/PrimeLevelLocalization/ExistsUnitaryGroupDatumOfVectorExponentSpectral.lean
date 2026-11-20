import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SameKTrans
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PFrameEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CenExHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PLevBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PPrimeProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PSiteTriv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SpanLePow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PStabOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PNearNbhd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PGoodOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PCongOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PProjLev
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PInIdUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.SatCard
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.NhdsBasisLevelSubgroup

namespace UpperTheory.Gal.Int.Geo.Pl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tjOK_holds : TjOK := tjOK_of sides_holds dict_holds levBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tjIdx_holds : TjIdx := tjIdx_of sides_holds dict_holds levBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem memEx_holds : MemEx := memEx_of sides_holds dict_holds levBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siteTriv_holds : SiteTriv := siteTriv_of sides_holds levBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siteEx_holds : SiteEx :=
  siteEx_of sides_holds dict_holds levBasic_holds (stabOf_of nearNbhd_holds primeProj_holds dict_holds)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem goodOf_holds : GoodOf :=
  goodOf_of levBasic_holds tjOK_holds (projLev_of dict_holds primeProj_holds levBasic_holds inIdUnit_holds)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem congOf_holds : CongOf := congOf_of levBasic_holds tjOK_holds tjIdx_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_unitaryGroupDatum_of_vector_exponent_spectral (h1 : VecEx) (h2 : ExpOf) (h3 : SpecTop) : PlanEx :=
  planEx_of ⟨frameEx_holds, h1, h3, h2, sides_holds, levBasic_holds, memEx_holds, siteTriv_holds, siteEx_holds, goodOf_holds,
    congOf_holds, datEx_holds, CertificateRingHomMap.rootsAlg_holds, satCard, intCof_holds⟩

end UpperTheory.Gal.Int.Geo.Pl
