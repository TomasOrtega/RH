import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.MatchAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceSubgroupIndicatorWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTwistedConstantTermMatches

namespace PositivityTheory.Rg.BcB.F.MatchAll

open PositivityTheory.Rg.Bc.ArchbcB.B

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hM2 : M2 := @GlobalTheory.CongMatch.match_principal_congruence_inert

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hM3 : M3 := @GlobalTheory.BCT.SplitCtMatch.match_ctMu_of_isSplitAt

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMB2₀ : MLM.MatchLMB2 := matchLMB2 hM2 hM3 hM4

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMWordS₀ : MLM.MatchLMWordS := matchLMWordS hM3

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMWord₀ : MLM.MatchLMWord := matchLMWord hM3

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMUnit₀ : MLM.MatchLMUnit := matchLMUnit hM1 hM3

end PositivityTheory.Rg.BcB.F.MatchAll
