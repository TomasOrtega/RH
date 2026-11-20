import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ChainRuleFormalGroupVar
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.XPowSuccDvdOfDerivative

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
The claim follows from `z_series_map_spec`.
-/
theorem zMap : ZMap.{u, v} := z_series_map_spec
/- English proof (translation)
The claim follows from `jet_mem'`.
-/
theorem jetMem : JetMem.{u} := jet_mem'
/- English proof (translation)
The claim follows from `weierstrass_p_prime_shape`.
-/
theorem wpPrimeShape : WpPrimeShape.{u} := weierstrass_p_prime_shape

/- English proof (translation)
The claim follows from `expSeriesAdd`.
-/
theorem expAdd : ExpAdd.{u} := expSeriesAdd
/- English proof (translation)
The claim follows from `plusZCleared_of plusZ tInZ`.
-/
theorem plusZCleared : PlusZCleared.{u} := plusZCleared_of plusZ tInZ

end Formalism.L2.Th1.A
