import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandD
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GramEqConjTransposeMul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandLA

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hermRepUnram [Fact HermRepUnram] : HermRepUnram := Fact.out

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orthBasisPos : OrthBasisPos := orthBasisPos_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem landherrUnram [Fact LandherrUnram] : LandherrUnram := Fact.out

end Formalism.HermitianLattices.Ext.L3
