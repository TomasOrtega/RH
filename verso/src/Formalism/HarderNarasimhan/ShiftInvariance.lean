import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNExtreme
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PiSumForallInsertOnly
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RescaleCovol
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameHermSharpB
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl

namespace Formalism.HN

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem satR : SatR := real_saturation_property
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finSup : FinSup := finite_supremum_slopes
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem satBasic : SatBasic := saturation_basic_properties
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ratioMax : RatioMax := maximal_slope_ratio
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degSupermod : DegSupermod := degree_supermodular
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem muChar : MuChar := slope_characterization
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hnStep_spec : HNStep := hnStep_of degSupermod muChar ratioMax finSup satR satBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem slopeIneq : SlopeIneq := slope_inequality_general
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hnSum : HNSum := polygon_slope_sum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hnSlopes : HNSlopes := polygon_slopes_characterization
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shiftInvariance : ShiftInvariance := shiftInvariance_of muChar muChar hnSlopes
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem duality : Duality := slope_duality_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem piSum : PiSum := product_slope_sum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plLat : PlLat := place_lattice_structure
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sizeMu : SizeMu := size_maximal_slope
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gramBlock : GramBlock := gram_block_determinant
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rescaleCovol : RescaleCovol := rescale_covolume_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twist : Twist := twist_of rescaleCovol plLat shiftInvariance
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem slopeIneqMean : SlopeIneqMean := slope_inequality_mean
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem htGram : HtGram := height_gram_determinant
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem htImage : HtImage := height_image_formula
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sizeIneq : SizeIneq := sizeIneq_of size_maximal_slope height_image_formula place_lattice_structure
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rerealize : Rerealize := lattice_rerealization
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quotRealize : QuotRealize := quotient_lattice_realization
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem theoremFSharp : TheoremFSharp := frame_theorem_sharp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem theoremF : TheoremF := frame_theorem_log_ideal
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualPl : DualPl := dual_polygon_identity

end Formalism.HN
