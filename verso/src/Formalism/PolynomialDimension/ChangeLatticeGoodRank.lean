import Formalism.PolynomialDimension.MultinomialDepth.SegmentHypOfIntervalHyp
import Formalism.PolynomialDimension.MultinomialDepth.SegmentTopRoomPublished
import Formalism.PolynomialDimension.MultinomialDepth.SegmentBoundThreeHolds

namespace Formalism.CountingSumsFrames.Top

/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_hyp_of_interval_hyp`.
-/
theorem hypSegOfHypI : Formalism.CountingSumsFrames.HypSegOfHypI := Formalism.CountingSumsFrames.segment_hyp_of_interval_hyp
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_log_bound`.
-/
theorem segLg : Formalism.CountingSumsFrames.SegLg := Formalism.CountingSumsFrames.segment_log_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_degree_sum_bound`.
-/
theorem segDegreeSum : Formalism.CountingSumsFrames.SegDegreeSum := Formalism.CountingSumsFrames.segment_degree_sum_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_terms_above_bound`.
-/
theorem segTermsAboveS : Formalism.CountingSumsFrames.SegTermsAboveS := Formalism.CountingSumsFrames.segment_terms_above_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_window_class`.
-/
theorem segWindowClass : Formalism.CountingSumsFrames.SegWindowClass := Formalism.CountingSumsFrames.segment_window_class
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_no_short_window`.
-/
theorem segNoShortWindow : Formalism.CountingSumsFrames.SegNoShortWindow := Formalism.CountingSumsFrames.segment_no_short_window
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_short_window_free`.
-/
theorem segShortWindowNoTie : Formalism.CountingSumsFrames.SegShortWindowNoTie := Formalism.CountingSumsFrames.segment_short_window_free
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_epsilon_bound`.
-/
theorem segEps : Formalism.CountingSumsFrames.SegEps := Formalism.CountingSumsFrames.segment_epsilon_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_epsilon_plus`.
-/
theorem segEpsPlus : Formalism.CountingSumsFrames.SegEpsPlus := Formalism.CountingSumsFrames.segment_epsilon_plus
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_depth_bound`.
-/
theorem segDepth : Formalism.CountingSumsFrames.SegDepth := Formalism.CountingSumsFrames.segment_depth_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_depth_sum_bound`.
-/
theorem segDepthSum : Formalism.CountingSumsFrames.SegDepthSum := Formalism.CountingSumsFrames.segment_depth_sum_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_initial_kappa`.
-/
theorem segKap0 : Formalism.CountingSumsFrames.SegKap0 := Formalism.CountingSumsFrames.segment_initial_kappa
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_top_room`.
-/
theorem segSTopRoom : Formalism.CountingSumsFrames.SegSTopRoom := Formalism.CountingSumsFrames.segment_top_room
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_top_room₂`.
-/
theorem segSTopRoom' : Formalism.CountingSumsFrames.SegmentTopRoom := Formalism.CountingSumsFrames.segment_top_room₂
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_size_bound`.
-/
theorem segSize : Formalism.CountingSumsFrames.SegSize := Formalism.CountingSumsFrames.segment_size_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.binomial_ratio_exp_bound`.
-/
theorem binomRatioExp : Formalism.CountingSumsFrames.BinomRatioExp := Formalism.CountingSumsFrames.binomial_ratio_exp_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_window_ratio`.
-/
theorem segWindowRatio : Formalism.CountingSumsFrames.SegWindowRatio := Formalism.CountingSumsFrames.segment_window_ratio
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_window_dimensions`.
-/
theorem segWindowDims : Formalism.CountingSumsFrames.SegWindowDims := Formalism.CountingSumsFrames.segment_window_dimensions
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_ratio_usage`.
-/
theorem useSegRatio : Formalism.CountingSumsFrames.UseSegRatio := Formalism.CountingSumsFrames.segment_ratio_usage
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_extension_window`.
-/
theorem segExtWindow : Formalism.CountingSumsFrames.SegExtWindow := Formalism.CountingSumsFrames.segment_extension_window
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_extension_bound`.
-/
theorem segExtB : Formalism.CountingSumsFrames.SegExtB := Formalism.CountingSumsFrames.segment_extension_bound
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.digit_vectors_count`.
-/
theorem digitVectorsCount : Formalism.CountingSumsFrames.DigitVectorsCount := Formalism.CountingSumsFrames.digit_vectors_count
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.digit_double_count`.
-/
theorem digitDoubleCount : Formalism.CountingSumsFrames.DigitDoubleCount := Formalism.CountingSumsFrames.digit_double_count
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.mean_share_first`.
-/
theorem meanShareA : Formalism.CountingSumsFrames.MeanShareA := Formalism.CountingSumsFrames.mean_share_first
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.mean_share_second`.
-/
theorem meanShareB : Formalism.CountingSumsFrames.MeanShareB := Formalism.CountingSumsFrames.mean_share_second
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_share_sum`.
-/
theorem segShareSum : Formalism.CountingSumsFrames.SegShareSum := Formalism.CountingSumsFrames.segment_share_sum
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.partner_converse`.
-/
theorem partnerConverse : Formalism.CountingSumsFrames.PartnerConverse := Formalism.CountingSumsFrames.partner_converse
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.change_lattice_good_rank`.
-/
theorem changeLatticeGoodRank : Formalism.CountingSumsFrames.ChangeLatticeGoodRank := Formalism.CountingSumsFrames.change_lattice_good_rank
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.direct_sum_good_rank`.
-/
theorem directSumGoodRank : Formalism.CountingSumsFrames.DirectSumGoodRank := Formalism.CountingSumsFrames.direct_sum_good_rank
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.direct_sum_partners`.
-/
theorem directSumPartners : Formalism.CountingSumsFrames.DirectSumPartners := Formalism.CountingSumsFrames.direct_sum_partners
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.det_leading_diagonal`.
-/
theorem detLeadDiag : Formalism.CountingSumsFrames.DetLeadDiag := Formalism.CountingSumsFrames.det_leading_diagonal
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.segment_bound_three_holds`.
-/
theorem segment_bound_three : Formalism.CountingSumsFrames.DigitSumValuationBound := Formalism.CountingSumsFrames.segment_bound_three_holds

end Formalism.CountingSumsFrames.Top
