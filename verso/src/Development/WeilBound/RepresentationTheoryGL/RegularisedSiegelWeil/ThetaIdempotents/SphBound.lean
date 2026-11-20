import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfoldingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisensteinStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeightsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeightsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEtaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeightsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaConditionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleRealityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement

namespace PositivityTheory.Rg.Rsw

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mapsExist : MapsExist := GlobalTheory.T.jacobi_maps_exist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem htExist : HtExist := GlobalTheory.T.height_functions_exist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem heckeEta : HeckeEta := GlobalTheory.T.hecke_character_eta_condition
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fjEis : FJEis := GlobalTheory.T.fourier_jacobi_eisenstein GlobalTheory.T.fourier_jacobi_unfolding GlobalTheory.T.theta_twist_identity
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pcBound : PcBound := GlobalTheory.T.partial_constant_term_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rSec : RSec := GlobalTheory.T.regular_section_of_heights htExist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eisHol : EisHol := GlobalTheory.T.eisenstein_holomorphy_of_heights htExist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thTotal : ThTotal := GlobalTheory.T.theta_total_of_hecke_eta heckeEta
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cfFJ : CfFJ := GlobalTheory.T.fourier_jacobi_coefficient_of_bound pcBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pcFc : PcFc := GlobalTheory.T.partial_constant_fourier_coefficient mapsExist GlobalTheory.T.fourier_zero_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sphBound : SphBound := GlobalTheory.T.spherical_bound_of_heights htExist
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resMu : ResMu :=
  GlobalTheory.T.residue_measure_identity mapsExist htExist heckeEta fjEis pcBound rSec eisHol thTotal pcFc sphBound GlobalTheory.T.fourier_zero_holds GlobalTheory.T.coefficient_data_exists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem polar : Polar :=
  GlobalTheory.T.polar_part_identity mapsExist htExist heckeEta GlobalTheory.T.right_identity_statement GlobalTheory.T.pole_reality fjEis pcBound rSec eisHol thTotal cfFJ pcFc sphBound

end PositivityTheory.Rg.Rsw
