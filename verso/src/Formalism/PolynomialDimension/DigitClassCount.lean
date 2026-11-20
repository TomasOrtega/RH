import Formalism.PolynomialDimension.MultinomialDepth.LemmaS
import Formalism.PolynomialDimension.MultinomialDepth.HarmonicLevelCountRec
import Formalism.PolynomialDimension.MultinomialDepth.BinomialSeriesBound
import Formalism.PolynomialDimension.MultinomialDepth.WeylDimPosOfAntitone
import Formalism.PolynomialDimension.MultinomialDepth.HockeyStickIdentity

namespace Formalism.CountingSumsFrames.Top

/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.wach_cohomology_top_S`.
-/
theorem lemmaS : Formalism.CountingSumsFrames.LemmaS := Formalism.CountingSumsFrames.wach_cohomology_top_S
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.count_B_formula`.
-/
theorem countB : Formalism.CountingSumsFrames.CountB := Formalism.CountingSumsFrames.count_B_formula
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.harmonic_level_count`.
-/
theorem levelCount : Formalism.CountingSumsFrames.LevelCount := Formalism.CountingSumsFrames.harmonic_level_count
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.highLevelTail`.
-/
theorem levelTail : Formalism.CountingSumsFrames.LevelTail := Formalism.CountingSumsFrames.highLevelTail
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.level_tail_exp_bound`.
-/
theorem levelTailExp : Formalism.CountingSumsFrames.LevelTailExp := Formalism.CountingSumsFrames.level_tail_exp_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.harmonic_lower_bound`.
-/
theorem harLower : Formalism.CountingSumsFrames.HarLower := Formalism.CountingSumsFrames.harmonic_lower_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.binomial_ratio_bound`.
-/
theorem binomRatio : Formalism.CountingSumsFrames.BinomRatio := Formalism.CountingSumsFrames.binomial_ratio_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.binomial_series_bound`.
-/
theorem binomSeries : Formalism.CountingSumsFrames.BinomSeries := Formalism.CountingSumsFrames.binomial_series_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.binomial_tail_bound`.
-/
theorem binomTail : Formalism.CountingSumsFrames.BinomTail := Formalism.CountingSumsFrames.binomial_tail_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.density_lower_bound`.
-/
theorem densityLower : Formalism.CountingSumsFrames.DensityLower := Formalism.CountingSumsFrames.density_lower_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.cloud_dimensions_bound`.
-/
theorem cloudDims : Formalism.CountingSumsFrames.CloudDims := Formalism.CountingSumsFrames.cloud_dimensions_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.cloud_share_bound`.
-/
theorem cloudShare : Formalism.CountingSumsFrames.CloudShare := Formalism.CountingSumsFrames.cloud_share_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.hockey_stick_identity`.
-/
theorem hockeyStick : Formalism.CountingSumsFrames.HockeyStick := Formalism.CountingSumsFrames.hockey_stick_identity
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.digit_class_count`.
-/
theorem digitClassCount : Formalism.CountingSumsFrames.DigitClassCount := Formalism.CountingSumsFrames.digit_class_count
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.digit_class_size`.
-/
theorem digitClassSize : Formalism.CountingSumsFrames.DigitClassSize := Formalism.CountingSumsFrames.digit_class_size

end Formalism.CountingSumsFrames.Top
