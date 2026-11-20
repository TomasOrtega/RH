import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.GeneratorPowSplitPlacesOfIdempotent
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBPf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SplitPlacePowersOfLocalOps
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.MultiplicityOneBase.ArchimedeanBaseChangeFirst
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.ArchimedeanBaseChangeFourth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplicationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplicationStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchTorusOfTwistedMatching
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBadIOf2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.LeviMatchingBlocks.StabilizerDilationWeightsDualIsotropicVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOfStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOfStatement

namespace PositivityTheory.Rg.BcB.F.MatchAll

open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcN.F2.LocOpPf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ctMul : MT.CtMul := GlobalTheory.T.constant_term_multiplicative

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fuMul : MT.FUMul := GlobalTheory.T.finite_unitary_multiplication

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dcosMul : MT.DcosMul := GlobalTheory.T.double_coset_multiplication

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hM4 : M4 := archimedean_base_change_fourth

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hM1 : M1 := m1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchT_of (h4 : M4) : MT.MatchT := TorusMatching.match_torus_of_twisted_matching h4

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchT : MT.MatchT := matchT_of archimedean_base_change_fourth

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchUnitI_of (h1 : M1) : MB.MatchUnitI := MB.matchUnitIOf h1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchUnitI : MB.MatchUnitI := matchUnitI_of m1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchSplit (h3 : M3) : MT.MatchSplit := GlobalTheory.T.matching_split_of h3 ctMul

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMId : MLM.MatchLMId := MLM.matchLMIdOf idemAlg BlockFiniteConvolution.locOk₀

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem macInv : MLM.MacInv := MLM.macInvOf locOp3 idemAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem generator_pow_split_places : MLM.SplitPlaceGeneratorPowers := MLM.generator_pow_split_places_of_idempotent idemAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMWord (h3 : M3) : MLM.MatchLMWord := MLM.matchLMWordOf (matchSplit h3) ctMul sphComm idemAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMWordS (h3 : M3) : MLM.MatchLMWordS := MLM.matchLMWordSOf (matchSplit h3) ctMul MLM.ctStar sphComm idemAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMUnit (h1 : M1) (h3 : M3) : MLM.MatchLMUnit := MLM.matchLMUnitOf (matchUnitI_of h1) (matchSplit h3) idemAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matchLMB2 (h2 : M2) (h3 : M3) (h4 : M4) : MLM.MatchLMB2 :=
  MLM.matchLMB3Of_pf (matchT_of h4) (MS.match_split_place_of_powers h3 (MS.split_place_powers_of_local_ops locOp3)) (MB.matchBadSOf h3 MB.lponeIdem)
    (MB.matchBadIOf2 h2 MB.lponeIdem) MB.fixIdem idemAlg

end PositivityTheory.Rg.BcB.F.MatchAll
