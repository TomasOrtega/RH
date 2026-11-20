import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.ExistsGaloisRepRankTwoOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TIsoOfFrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.SV
/- English proof (translation)
Introduce `P F Ω _ _ _ _ _ _ l _ ι n _ hn π χ hreg hpol`. Take `⟨r, wt, HT, H⟩` from `_root_.UpperTheory.Gal.SV.gr2S' P.galR F Ω l ι n hn π χ hreg hpol`. Establish `key` using `H.frob`. Establish `hsm : GlobalTheory.PRep.IsSmooth π.finPart` using `fun v => by`. Use `(π.cusp v.1 v.2).1.level using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `k`. Conclude with `Subtype.ext_iff`. Establish `: Nontrivial π.V` using `Submodule.nontrivial_iff_ne_bot.2 π.ne_bot`. Use `⟨r, wt, HT, H, ⟨H.ss, ?_⟩, fun r' hr' ha => galRS_iso H ha.1 ?_⟩` and prove the remaining obligations. Use `filter_upwards [sat_ae_of_smooth (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart hsm fun w =>`.

Set `⟨⟨σ, hσ⟩, hiso⟩` to `_root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F n π w`. Use the proof step `⟨σ, hiso σ hσ⟩, eventually_not_mem F l] with w ⟨B, hB⟩ hw`. Conclude with `⟨B, hB, key w hw B hB⟩`. Use `_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P F Ω l ι n r r' H.cont hr' H.ss ha.1 ?_ filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw` and prove the remaining obligations. Conclude with `⟨_, key w hw B hB, hf⟩`.
-/
theorem exRS_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → ExRS := by
  intro P F Ω _ _ _ _ _ _ l _ ι n _ hn π χ hreg hpol
  obtain ⟨r, wt, HT, H⟩ := _root_.UpperTheory.Gal.SV.gr2S' P.galR F Ω l ι n hn π χ hreg hpol
  have key := H.frob
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  refine ⟨r, wt, HT, H, ⟨H.ss, ?_⟩, fun r' hr' ha => galRS_iso H ha.1 ?_⟩
  · filter_upwards [sat_ae_of_smooth (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart hsm fun w =>
      let ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F n π w
      ⟨σ, hiso σ hσ⟩, eventually_not_mem F l] with w ⟨B, hB⟩ hw
    exact ⟨B, hB, key w hw B hB⟩
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P F Ω l ι n r r' H.cont hr' H.ss ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw
    exact ⟨_, key w hw B hB, hf⟩
end UpperTheory.Gal.SV
end
end
