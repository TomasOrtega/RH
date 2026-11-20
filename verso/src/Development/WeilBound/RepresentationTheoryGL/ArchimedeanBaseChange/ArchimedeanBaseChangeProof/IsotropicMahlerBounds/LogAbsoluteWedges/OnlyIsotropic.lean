import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlacesStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundFinitePlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSizeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisGStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparisonStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTermOfIsotropicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightSupportBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightTranslationStatement

namespace PositivityTheory.Rg.BcB.D1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulF : MulF := GlobalTheory.T.multiplicativity_finite_places
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem detMono : DetMono := GlobalTheory.T.determinant_monotonicity
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulI : MulI := GlobalTheory.T.multiplicativity_infinite_places detMono
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wedgeF : WedgeF := GlobalTheory.T.wedge_bound_finite_places mulF
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wedgeI : WedgeI := GlobalTheory.T.wedgeI_of_detMono_mulI_var detMono mulI
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wedgeSub : WedgeSub := GlobalTheory.T.wedge_subspace_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairF : PairF := GlobalTheory.T.pairing_bound_finite_places mulF
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairI : PairI := GlobalTheory.T.pairing_bound_infinite_places detMono
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logAbsBasic : LogAbsBasic := GlobalTheory.T.log_abs_basic_facts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem szFin : SzFin := GlobalTheory.T.size_finite_places
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finSupp : FinSupp := GlobalTheory.T.finite_support_of_size mulF mulI szFin
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degAdelic : DegAdelic := GlobalTheory.T.adelic_degree_formula mulF mulI logAbsBasic finSupp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degBasisG : DegBasisG := GlobalTheory.T.degree_basis_general wedgeF wedgeI mulF mulI logAbsBasic finSupp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degBasis : DegBasis := GlobalTheory.T.degBasis_of_degBasisG' degBasisG
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degSubmod : DegSubmod := GlobalTheory.T.degree_submodule_bound wedgeF wedgeI wedgeSub finSupp degBasisG GlobalTheory.T.two_bases_comparison
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degRat : DegRat := GlobalTheory.T.degree_rational_subspace degBasisG
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degMove : DegMove := GlobalTheory.T.degree_under_translation mulF mulI szFin finSupp degBasisG
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degBdd : DegBdd := GlobalTheory.T.degree_bounded_of_basis wedgeF wedgeI mulF mulI szFin finSupp logAbsBasic degBasisG
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conjPlaces : ConjPlaces := GlobalTheory.T.conjugate_places_facts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sizeBasic : SizeBasic := GlobalTheory.T.size_basic_of_conj_places szFin conjPlaces
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degPairing : DegPairing :=
  GlobalTheory.T.degree_pairing_identity wedgeF wedgeI mulF mulI pairF pairI szFin finSupp logAbsBasic conjPlaces degBasisG GlobalTheory.T.radical_subspace_facts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mahler_of_c (h : MahlerC) : Mahler := GlobalTheory.T.mahler_bound_of_degree degBdd degRat h
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mahler : Mahler := mahler_of_c (PositivityTheory.Rg.BcB.E1.mahlerC_of_deg degBasis degAdelic degBdd degRat)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem onlyStable : OnlyStable := GlobalTheory.T.only_stable_subspaces degSubmod degMove degBdd degPairing sizeBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem onlyIsotropic : OnlyIsotropic := GlobalTheory.T.only_isotropic_subspaces onlyStable degPairing sizeBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ellTerm : EllTerm := GlobalTheory.T.elliptic_term_of_isotropic onlyIsotropic
/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem chainSum : ChainSum := fun m =>
  ⟨GlobalTheory.T.sign_cone_weight_indicator m, GlobalTheory.T.sign_cone_weight_support_bound m, (GlobalTheory.T.sign_cone_weight_translation m).1, (GlobalTheory.T.sign_cone_weight_translation m).2.1, (GlobalTheory.T.sign_cone_weight_translation m).2.2⟩

end PositivityTheory.Rg.BcB.D1
