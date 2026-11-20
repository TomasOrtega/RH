import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplitHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OrdGen
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsHeckeCorrespondenceOnIntegralShimuraModel
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPIsogenyKernelEqSubgroupScheme
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MEsNorm

namespace UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem esGen_link : EsGen := UpperTheory.Cb.exists_heckeCorrespondence_on_integral_shimuraModel
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem esNorm_link : EsNorm := esNorm_of esGen_link
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ordGen_link : OrdGen := UpperTheory.Gal.Ord.ordGen
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quotObj_link : QuotObj := UpperTheory.Cb.exists_pIsogeny_kernel_eq_subgroupScheme
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem congKS_link : CongKS := congKS_holds esNorm_link esGen_link ordGen_link quotObj_link

end UpperTheory.Gal.crystallineComparison.Mod
