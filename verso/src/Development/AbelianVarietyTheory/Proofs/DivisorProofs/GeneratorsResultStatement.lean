import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorsResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HalfGeo.GensProof.gens | exact GlobalTheory.HalfGeo.GensProof.gens | (intros; apply GlobalTheory.HalfGeo.GensProof.gens <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.generators_result : GensSt := by
  first | exact @GlobalTheory.HalfGeo.GensProof.gens | exact GlobalTheory.HalfGeo.GensProof.gens | (intros; apply GlobalTheory.HalfGeo.GensProof.gens <;> assumption)
