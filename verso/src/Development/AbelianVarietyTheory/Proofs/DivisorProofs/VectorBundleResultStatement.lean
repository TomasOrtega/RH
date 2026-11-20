import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfGeo.bundleSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVectorBundleResult.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.vector_bundle_result : BundleSt := by
  first | exact @GlobalTheory.HalfGeo.bundleSt | exact GlobalTheory.HalfGeo.bundleSt | (intros; apply GlobalTheory.HalfGeo.bundleSt <;> assumption)
