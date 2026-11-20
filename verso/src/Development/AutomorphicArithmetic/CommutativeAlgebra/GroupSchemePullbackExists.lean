import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
open UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `G R _ _ gb N X X' s e o`. Conclude with `GlobalTheory.UPel.HT.Gen.BaseChange.exists_gObjMap_pull e o`.
-/
theorem UpperTheory.group_scheme_pullback_exists :
    GPull := by
  intro G R _ _ gb N X X' s e o
  exact GlobalTheory.UPel.HT.Gen.BaseChange.exists_gObjMap_pull e o
