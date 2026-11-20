import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTRangeA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTGlue
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PrimeCountOfPsi
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTSharp
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsm
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDens
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMain
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSumL
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHB

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

/- English proof (translation)
The claim follows from `smoothed_explicit_formula`.
-/
theorem explicitS_proof' : ExplicitS := smoothed_explicit_formula

/- English proof (translation)
The claim follows from `Dens.log_density_bound`.
-/
theorem logDensityM_proof' : LogDensityM := Dens.log_density_bound

/- English proof (translation)
The claim follows from `deuring_heilbronn_lossy`.
-/
theorem deuringHeilbronnMB_proof' : DeuringHeilbronnMB := deuring_heilbronn_lossy

/- English proof (translation)
The claim follows from `prime_count_of_psi (glue_ranges psi_relative_near_range (psi_relative_far_range explicitS_proof' differenced_explicit_formula (zero_sum_bound_lossy logDensityM_proof' deuringHeilbronnMB_proof')))`.
-/
theorem pnt_progressions_relative_weak_holds : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW :=
  prime_count_of_psi (glue_ranges psi_relative_near_range
    (psi_relative_far_range explicitS_proof' differenced_explicit_formula (zero_sum_bound_lossy logDensityM_proof' deuringHeilbronnMB_proof')))

end Formalism.HermitianLattices.Ext.PrimesInProgressions
