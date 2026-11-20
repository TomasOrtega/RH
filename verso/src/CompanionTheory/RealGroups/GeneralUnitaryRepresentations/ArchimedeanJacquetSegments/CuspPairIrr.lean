import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ComapTwKer
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.DerFin
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.JacquetModuleThetaTwist
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.NontrivialOfIsIrreducible
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPair
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHoldsStatement

namespace CompanionTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nuPair : GlobalTheory.BZSeg.NuPair k :=
  nuPair_of k (GlobalTheory.T.derivative_jacquet_holds k GlobalTheory.CompanionTheory.BZCuspPair.irrAdm) (jmTheta k) (derFin_of k (derEquiv k))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cuspPairIrr : GlobalTheory.BZSeg.CuspPairIrr k := cuspPairIrr_of k (nuPair k)

end CompanionTheory.RgGu.NR
