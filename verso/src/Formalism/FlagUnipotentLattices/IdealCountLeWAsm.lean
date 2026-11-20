import Formalism.FlagUnipotentLattices.IdealCountLeW
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ColonCountWeighted

namespace Formalism.HermitianLatticeCounting.Final.S6

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.embedding_dual_compatible`.
-/
theorem iotaDual : Formalism.HermitianLatticeCounting.S6.IotaDual := Formalism.HermitianLatticeCounting.P.embedding_dual_compatible
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.embedding_determined_by_restriction`.
-/
theorem iotaDetermined : Formalism.HermitianLatticeCounting.S6.IotaDetermined := Formalism.HermitianLatticeCounting.P.embedding_determined_by_restriction
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.dual_lattice_index`.
-/
theorem dualIndex : Formalism.HermitianLatticeCounting.S6.DualIndex := Formalism.HermitianLatticeCounting.P.dual_lattice_index
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.submodule_generator_count`.
-/
theorem subGen : Formalism.HermitianLatticeCounting.S6.SubGen := Formalism.HermitianLatticeCounting.P.submodule_generator_count
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.extension_generator_count`.
-/
theorem extGen : Formalism.HermitianLatticeCounting.S6.ExtGen := Formalism.HermitianLatticeCounting.P.extension_generator_count
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.colon_ideal_scaling`.
-/
theorem colonScale : Formalism.HermitianLatticeCounting.S6.ColonScale := Formalism.HermitianLatticeCounting.P.colon_ideal_scaling
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.colon_ideal_norm`.
-/
theorem colonNorm : Formalism.HermitianLatticeCounting.S6.ColonNorm := Formalism.HermitianLatticeCounting.P.colon_ideal_norm
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.ideal_count_eq`.
-/
theorem idealCountEq : Formalism.HermitianLatticeCounting.S6.IdealCountEq := Formalism.HermitianLatticeCounting.P.ideal_count_eq
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.quotient_card`.
-/
theorem idealCountLe : Formalism.HermitianLatticeCounting.S6.IdealCountLe := Formalism.HermitianLatticeCounting.P.quotient_card
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.totient_bound_alt`.
-/
theorem totientBound : Formalism.HermitianLatticeCounting.S6.TotientBound := Formalism.HermitianLatticeCounting.P.totient_bound_alt
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.torsion_bound_alt`.
-/
theorem torsionBound : Formalism.HermitianLatticeCounting.S6.TorsionBound := Formalism.HermitianLatticeCounting.P.torsion_bound_alt
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.colon_count_bound`.
-/
theorem cCount : Formalism.HermitianLatticeCounting.S6.CCount := Formalism.HermitianLatticeCounting.P.colon_count_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.colon_count_of_hyp`.
-/
theorem cCount' : Formalism.HermitianLatticeCounting.S6.CCountAsm := Formalism.HermitianLatticeCounting.P.colon_count_of_hyp
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted`.
-/
theorem idealCountLeW : Formalism.HermitianLatticeCounting.S6.IdealCountLeW := Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted_of_hyp`.
-/
theorem idealCountLeWAsm : Formalism.HermitianLatticeCounting.S6.IdealCountLeW' := Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted_of_hyp
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.colon_count_weighted`.
-/
theorem cCountW : Formalism.HermitianLatticeCounting.S6.CCountW := Formalism.HermitianLatticeCounting.P.colon_count_weighted
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.colon_count_weighted_of_hyp`.
-/
theorem cCountWAsm : Formalism.HermitianLatticeCounting.S6.CCountWAsm := Formalism.HermitianLatticeCounting.P.colon_count_weighted_of_hyp
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.torsion_bound_of_totient`.
-/
theorem torsionBoundAsm : Formalism.HermitianLatticeCounting.S6.TorsionBoundAsm := Formalism.HermitianLatticeCounting.P.torsion_bound_of_totient
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.height_loss_bound`.
-/
theorem quotCard : Formalism.HermitianLatticeCounting.S6.QuotCard := Formalism.HermitianLatticeCounting.P.height_loss_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.cost_bound`.
-/
theorem costBound : Formalism.HermitianLatticeCounting.S6.CostBound := Formalism.HermitianLatticeCounting.P.cost_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.loss_bound_holds`.
-/
theorem hLoss : Formalism.HermitianLatticeCounting.S6.HLoss := Formalism.HermitianLatticeCounting.P.loss_bound_holds

end Formalism.HermitianLatticeCounting.Final.S6
