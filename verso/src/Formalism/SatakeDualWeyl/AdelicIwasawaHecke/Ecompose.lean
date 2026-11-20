import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

namespace Formalism.UG.P

/- English proof (translation)
The claim follows from `hecke_algebra_GL_comm_of_cartan cartan_decomposition_holds`.
-/
theorem hecke_algebra_GL_commutative : Formalism.UG.HeckeCommGL := hecke_algebra_GL_comm_of_cartan cartan_decomposition_holds

/- English proof (translation)
The claim follows from `satake_Tj_of_spherical_cosets exists_spherical_function Tj_double_coset_decomposition`.
-/
theorem satake_transform_hecke_operator_Tj : Formalism.UG.SatakeTj := satake_Tj_of_spherical_cosets exists_spherical_function Tj_double_coset_decomposition

end Formalism.UG.P
