import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBoundedOrbitHasNearbyFixedPoint.lean&line=211#L211)
-/
theorem _root_.GlobalTheory.T.bounded_orbit_has_nearby_fixed_point : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (x : Om l) (r : ℝ), (∀ g ∈ H, ‖g x - x‖ ≤ r) → ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ c * r := by
  first | exact @GlobalTheory.AxLemma.ax_lemma | exact GlobalTheory.AxLemma.ax_lemma | (intros; apply GlobalTheory.AxLemma.ax_lemma <;> assumption)
