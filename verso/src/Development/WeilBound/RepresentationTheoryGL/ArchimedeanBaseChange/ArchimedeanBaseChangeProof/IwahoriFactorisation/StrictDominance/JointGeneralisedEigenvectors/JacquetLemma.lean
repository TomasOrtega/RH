import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHoldsStatement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentOfProjectionZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantHeckeOperatorsCommute
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.CechDescentTests.A6
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LongWConjApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContractionStatement

noncomputable section

namespace PositivityTheory.SphericalProduct

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jacquet_hecke (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : A2 G :=
  GlobalTheory.T.jacquet_projection_hecke_holds G

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem iwahori_u : IwahoriU :=
  GlobalTheory.T.iwahori_unipotent_datum

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dom_u : DomU :=
  GlobalTheory.T.dominant_unipotent_contraction

end PositivityTheory.SphericalProduct

end
