import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Trzero
open UpperTheory.V.Sd.Eis

/- English proof (translation)
Introduce `F _ _ _ _ _ ω hω φ hφ v` and use `UpperTheory.V.Sd.Hm.trzero F ω hω φ hφ.cent v`.
-/
theorem UpperTheory.eisenstein_central_lie_action :
    UpperTheory.V.Sd.Eis.CentLie :=
  fun F _ _ _ _ _ ω hω φ hφ v => UpperTheory.V.Sd.Hm.trzero F ω hω φ hφ.cent v
