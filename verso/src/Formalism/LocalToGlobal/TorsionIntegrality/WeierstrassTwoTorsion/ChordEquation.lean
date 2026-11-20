import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ChainRuleFormalGroupVar
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.XPowSuccDvdOfDerivative

universe u v

namespace Formalism.L2.Th1.A

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zMap : ZMap.{u, v} := z_series_map_spec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetMem : JetMem.{u} := jet_mem'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpPrimeShape : WpPrimeShape.{u} := weierstrass_p_prime_shape

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expAdd : ExpAdd.{u} := expSeriesAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem plusZCleared : PlusZCleared.{u} := plusZCleared_of plusZ tInZ

end Formalism.L2.Th1.A
