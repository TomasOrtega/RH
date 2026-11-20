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
The claim follows from `real_saturation_property`.
-/
theorem satR : SatR := real_saturation_property
/- English proof (translation)
The claim follows from `finite_supremum_slopes`.
-/
theorem finSup : FinSup := finite_supremum_slopes
/- English proof (translation)
The claim follows from `saturation_basic_properties`.
-/
theorem satBasic : SatBasic := saturation_basic_properties
/- English proof (translation)
The claim follows from `maximal_slope_ratio`.
-/
theorem ratioMax : RatioMax := maximal_slope_ratio
/- English proof (translation)
The claim follows from `degree_supermodular`.
-/
theorem degSupermod : DegSupermod := degree_supermodular
/- English proof (translation)
The claim follows from `slope_characterization`.
-/
theorem muChar : MuChar := slope_characterization
/- English proof (translation)
The claim follows from `hnStep_of degSupermod muChar ratioMax finSup satR satBasic`.
-/
theorem hnStep_spec : HNStep := hnStep_of degSupermod muChar ratioMax finSup satR satBasic
/- English proof (translation)
The claim follows from `slope_inequality_general`.
-/
theorem slopeIneq : SlopeIneq := slope_inequality_general
/- English proof (translation)
The claim follows from `polygon_slope_sum`.
-/
theorem hnSum : HNSum := polygon_slope_sum
/- English proof (translation)
The claim follows from `polygon_slopes_characterization`.
-/
theorem hnSlopes : HNSlopes := polygon_slopes_characterization
/- English proof (translation)
The claim follows from `shiftInvariance_of muChar muChar hnSlopes`.
-/
theorem shiftInvariance : ShiftInvariance := shiftInvariance_of muChar muChar hnSlopes
/- English proof (translation)
The claim follows from `slope_duality_formula`.
-/
theorem duality : Duality := slope_duality_formula
/- English proof (translation)
The claim follows from `product_slope_sum`.
-/
theorem piSum : PiSum := product_slope_sum
/- English proof (translation)
The claim follows from `place_lattice_structure`.
-/
theorem plLat : PlLat := place_lattice_structure
/- English proof (translation)
The claim follows from `size_maximal_slope`.
-/
theorem sizeMu : SizeMu := size_maximal_slope
/- English proof (translation)
The claim follows from `gram_block_determinant`.
-/
theorem gramBlock : GramBlock := gram_block_determinant
/- English proof (translation)
The claim follows from `rescale_covolume_formula`.
-/
theorem rescaleCovol : RescaleCovol := rescale_covolume_formula
/- English proof (translation)
The claim follows from `twist_of rescaleCovol plLat shiftInvariance`.
-/
theorem twist : Twist := twist_of rescaleCovol plLat shiftInvariance
/- English proof (translation)
The claim follows from `slope_inequality_mean`.
-/
theorem slopeIneqMean : SlopeIneqMean := slope_inequality_mean
/- English proof (translation)
The claim follows from `height_gram_determinant`.
-/
theorem htGram : HtGram := height_gram_determinant
/- English proof (translation)
The claim follows from `height_image_formula`.
-/
theorem htImage : HtImage := height_image_formula
/- English proof (translation)
The claim follows from `sizeIneq_of size_maximal_slope height_image_formula place_lattice_structure`.
-/
theorem sizeIneq : SizeIneq := sizeIneq_of size_maximal_slope height_image_formula place_lattice_structure
/- English proof (translation)
The claim follows from `lattice_rerealization`.
-/
theorem rerealize : Rerealize := lattice_rerealization
/- English proof (translation)
The claim follows from `quotient_lattice_realization`.
-/
theorem quotRealize : QuotRealize := quotient_lattice_realization
/- English proof (translation)
The claim follows from `frame_theorem_sharp`.
-/
theorem theoremFSharp : TheoremFSharp := frame_theorem_sharp
/- English proof (translation)
The claim follows from `frame_theorem_log_ideal`.
-/
theorem theoremF : TheoremF := frame_theorem_log_ideal
/- English proof (translation)
The claim follows from `dual_polygon_identity`.
-/
theorem dualPl : DualPl := dual_polygon_identity

end Formalism.HN
