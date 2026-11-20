import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CircleIntegralInvSubEqZeroOfOutside
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.NormalisationIdentity

namespace Formalism.HermitianLatticeCounting.Final.ExpansionTerms

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.integral_norm_estimate_holds`.
-/
theorem integral_norm_estimate : Formalism.HermitianLatticeCounting.ExpansionTerms.AlgebraicIntegerNormGeOne := Formalism.HermitianLatticeCounting.P.integral_norm_estimate_holds
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.block_minor_sum_pow_sixty_four`.
-/
theorem component_total_sixty_four : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockMinorSumPowSixtyFour := Formalism.HermitianLatticeCounting.P.block_minor_sum_pow_sixty_four
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.integral_norm_application_holds`.
-/
theorem integral_norm_application : Formalism.HermitianLatticeCounting.ExpansionTerms.NormGeOneMaxBound := Formalism.HermitianLatticeCounting.P.integral_norm_application_holds
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.corollary_consequence_holds`.
-/
theorem corollary_consequence : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentBound₂ := Formalism.HermitianLatticeCounting.P.corollary_consequence_holds
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.moment_recursion_iterate`.
-/
theorem mass_inequality_iteration : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentRecursionIterate := Formalism.HermitianLatticeCounting.P.moment_recursion_iterate
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.abstract_iteration_theorem_holds`.
-/
theorem abstract_iteration_theorem : Formalism.HermitianLatticeCounting.ExpansionTerms.SuperharmonicMomentBound := Formalism.HermitianLatticeCounting.P.abstract_iteration_theorem_holds

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.invariant_value_holds`.
-/
theorem leadingMinorUnipotentInvariant : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorUnipotentInvariant := Formalism.HermitianLatticeCounting.P.invariant_value_holds
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.leading_minor_vanishes_off_block_ends`.
-/
theorem e4aVanish : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorVanishesOffBlockEnds := Formalism.HermitianLatticeCounting.P.leading_minor_vanishes_off_block_ends
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.leading_minor_at_block_end`.
-/
theorem e4aValue : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd := Formalism.HermitianLatticeCounting.P.leading_minor_at_block_end
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.orbit_integral_entries`.
-/
theorem integral_evaluation_fourth : Formalism.HermitianLatticeCounting.ExpansionTerms.OrbitIntegralEntries := Formalism.HermitianLatticeCounting.P.orbit_integral_entries
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.last_distance_lower_bound`.
-/
theorem majorant_lower_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.LastDistanceLowerBound := Formalism.HermitianLatticeCounting.P.last_distance_lower_bound

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.degree_ratio_minus_bound`.
-/
theorem degRatioMinus : Formalism.HermitianLatticeCounting.ExpansionTerms.DegRatioMinus := Formalism.HermitianLatticeCounting.P.degree_ratio_minus_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.degree_increment_bound`.
-/
theorem degStepBound : Formalism.HermitianLatticeCounting.ExpansionTerms.DegStepBound := Formalism.HermitianLatticeCounting.P.degree_increment_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.first_operator_norm_bound`.
-/
theorem sup_l2_ratio_majorant : Formalism.HermitianLatticeCounting.ExpansionTerms.supL2RatioMajorant := Formalism.HermitianLatticeCounting.P.first_operator_norm_bound

end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
