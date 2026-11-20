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
The claim follows from `Fact.out`.
-/
theorem hermRepUnram [Fact HermRepUnram] : HermRepUnram := Fact.out

/- English proof (translation)
The claim follows from `orthBasisPos_holds`.
-/
theorem orthBasisPos : OrthBasisPos := orthBasisPos_holds

/- English proof (translation)
The claim follows from `Fact.out`.
-/
theorem landherrUnram [Fact LandherrUnram] : LandherrUnram := Fact.out

end Formalism.HermitianLattices.Ext.L3
