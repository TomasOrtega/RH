import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatake
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa

namespace Formalism.UG.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem satake_inert : Formalism.UG.SatakeInert := satake_transform_inert_prime exists_spherical_function_unitary

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem satake_mul : Formalism.UG.SatMul := satake_transform_multiplicative exists_spherical_function_unitary

end Formalism.UG.P
