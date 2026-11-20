import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

namespace Formalism.UG.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hecke_algebra_GL_commutative : Formalism.UG.HeckeCommGL := hecke_algebra_GL_comm_of_cartan cartan_decomposition_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem satake_transform_hecke_operator_Tj : Formalism.UG.SatakeTj := satake_Tj_of_spherical_cosets exists_spherical_function Tj_double_coset_decomposition

end Formalism.UG.P
