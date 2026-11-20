import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroInertiaOfLanglands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDepthZeroInertiaOfLanglands.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.depth_zero_inertia_of_langlands : GlobalTheory.Published.DepthZeroTypeInertia → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.DepthZeroInertia := by
  first | exact @GlobalTheory.DepthZeroBridge.depthZeroInertia_of_depthZeroTypeInertia | exact GlobalTheory.DepthZeroBridge.depthZeroInertia_of_depthZeroTypeInertia | (intros; apply GlobalTheory.DepthZeroBridge.depthZeroInertia_of_depthZeroTypeInertia <;> assumption)
