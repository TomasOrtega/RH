import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Formalism.FlagUnipotentLattices.SubmoduleGeneratorsBound
import Formalism.FlagUnipotentLattices.CoveringRadius2
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SumComplexEmbeddingsEqSumInfinitePlace
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumTupleOfLatticeSumTuple
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCoveringDivisor
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Residue

namespace Formalism.HermitianLatticeCounting.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dedekindZeta_residue_bound : Formalism.HermitianLatticeCounting.S7.DedekindZetaResidueBound := dedekind_residue_bound

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transference_principle : Formalism.HermitianLatticeCounting.LatticeSumBounds.Transference := transference_covering

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem covering_radius_bound₂ : Formalism.HermitianLatticeCounting.S7.CoveringRadius2 := transference_covering_divisor

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem covering_of_transference : Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := coveringO_of_transference transference_principle

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem covering_of_transference_variant : Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO' := coveringO'_of_transference transference_principle

end Formalism.HermitianLatticeCounting.P
