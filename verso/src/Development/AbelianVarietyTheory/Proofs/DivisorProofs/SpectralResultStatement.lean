import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpectralResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HalfGeo.SpecProof.specSt | exact GlobalTheory.HalfGeo.SpecProof.specSt | (intros; apply GlobalTheory.HalfGeo.SpecProof.specSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.spectral_result : SpecSt := by
  first | exact @GlobalTheory.HalfGeo.SpecProof.specSt | exact GlobalTheory.HalfGeo.SpecProof.specSt | (intros; apply GlobalTheory.HalfGeo.SpecProof.specSt <;> assumption)
