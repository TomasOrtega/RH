import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HalfGeo.bundleSt | exact GlobalTheory.HalfGeo.bundleSt | (intros; apply GlobalTheory.HalfGeo.bundleSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.vector_bundle_result : BundleSt := by
  first | exact @GlobalTheory.HalfGeo.bundleSt | exact GlobalTheory.HalfGeo.bundleSt | (intros; apply GlobalTheory.HalfGeo.bundleSt <;> assumption)
