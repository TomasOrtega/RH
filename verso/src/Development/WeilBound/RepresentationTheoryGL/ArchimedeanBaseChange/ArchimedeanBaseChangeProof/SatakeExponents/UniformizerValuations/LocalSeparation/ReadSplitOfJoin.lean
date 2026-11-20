import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.LeafSeparation.LeafModHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeModOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PReadModOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeSatOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PPairSat
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChiDetPowSplitCentre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfOfTwPart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatVMapMulChi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasInfCharGLRankZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisFurther
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmVecTranslate

namespace PositivityTheory.Rg.BcB.F.RS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem joinEx_holds : JoinEx := GlobalTheory.CompanionTheory.JoinDatum.joinEx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem joinInf_holds : JoinInf := GlobalTheory.CompanionTheory.JoinInfProof.joinInf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem joinSat_holds : JoinSat := GlobalTheory.CompanionTheory.JoinSatPf.joinSat

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem treeInf_holds : TreeInf := GlobalTheory.CompanionTheory.TreeInfSum.treeInf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weightJoin_holds : WeightJoin := GlobalTheory.CompanionTheory.WeightJoin.main

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem muLoc_holds' : MuLoc := GlobalTheory.CompanionTheory.MuLocal.muLoc_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem treeMod_of (h : JoinMod) : TreeMod := treeModOf_holds leafMod_holds GlobalTheory.CompanionTheory.NodeSep.nodeMod h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem readMod_of (h : JoinMod) : ReadMod := readModOf_holds (treeMod_of h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem readSplit_of_join (h : JoinMod) : ReadSplit :=
  readSplit_of (treeSatOf_holds (treeMod_of h)) pairSat_holds thetaSat2_holds GlobalTheory.CompanionTheory.CtS.ctSat muLoc_holds' joinSat_holds
    GlobalTheory.CompanionTheory.SatSplitAt.satSplit GlobalTheory.CompanionTheory.ConjSat.satConj

end PositivityTheory.Rg.BcB.F.RS
