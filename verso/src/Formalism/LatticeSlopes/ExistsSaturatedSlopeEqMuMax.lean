import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
import Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated
import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained
import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin
import Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum

namespace Formalism.F

/- English proof (translation)
The claim follows from `covol_eq_gram`.
-/
theorem covolEqGram : CovolEqGram := covol_eq_gram
/- English proof (translation)
The claim follows from `covol_pos'`.
-/
theorem covolPos : CovolPos := covol_pos'
/- English proof (translation)
The claim follows from `covol_basic_properties`.
-/
theorem covolBasic : CovolBasic := covol_basic_properties
/- English proof (translation)
The claim follows from `covol_eq_covolume'`.
-/
theorem covolEqCovolume : CovolEqCovolume := covol_eq_covolume'
/- English proof (translation)
The claim follows from `gram_det_le`.
-/
theorem gramDetLe : GramDetLe := gram_det_le
/- English proof (translation)
The claim follows from `slopesBdd_of gramDetLe`.
-/
theorem slopesBdd : SlopesBdd := slopesBdd_of gramDetLe
/- English proof (translation)
The claim follows from `slopeLeMuMax_of slopesBdd`.
-/
theorem slopeLeMuMax : SlopeLeMuMax := slopeLeMuMax_of slopesBdd
/- English proof (translation)
The claim follows from `muMaxMono_of slopesBdd`.
-/
theorem muMaxMono : MuMaxMono := muMaxMono_of slopesBdd
/- English proof (translation)
The claim follows from `degree_quotient`.
-/
theorem degQuot : DegQuot := degree_quotient
/- English proof (translation)
The claim follows from `covol_anti_same_rank`.
-/
theorem covolAntiSameRank : CovolAntiSameRank := covol_anti_same_rank
/- English proof (translation)
The claim follows from `saturation_properties`.
-/
theorem saturProps : SaturProps := saturation_properties
/- English proof (translation)
The claim follows from `shortVector_of covolEqCovolume`.
-/
theorem shortVector : ShortVector := shortVector_of covolEqCovolume
/- English proof (translation)
The claim follows from `finiteSaturated_of shortVector`.
-/
theorem finiteSaturated : FiniteSaturated := finiteSaturated_of shortVector
/- English proof (translation)
The claim follows from `muMaxLeMin_of covolPos shortVector`.
-/
theorem muMaxLeMin : MuMaxLeMin := muMaxLeMin_of covolPos shortVector
/- English proof (translation)
The claim follows from `orthogonal_sum_slope`.
-/
theorem orthSum : OrthSum := orthogonal_sum_slope

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/- English proof (translation)
The claim follows from `muMaxMono E L N ‹_› hN hN0`.
-/
theorem muMax_mono {L N : Submodule ℤ E} [DiscreteTopology L] (hN : N ≤ L) (hN0 : N ≠ ⊥) :
    muMax N ≤ muMax L :=
  muMaxMono E L N ‹_› hN hN0

/- English proof (translation)
The claim follows from `covolPos E L ‹_›`.
-/
theorem covol_pos (L : Submodule ℤ E) [DiscreteTopology L] : 0 < covol L :=
  covolPos E L ‹_›

/- English proof (translation)
The claim follows from `(degQuot E L N ‹_› hN).2.2`.
-/
theorem deg_eq_deg_add_deg_quot {L N : Submodule ℤ E} [DiscreteTopology L] (hN : IsSaturated L N) :
    deg L = deg N + deg (quot L N) :=
  (degQuot E L N ‹_› hN).2.2

end

end Formalism.F
