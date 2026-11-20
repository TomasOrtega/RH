import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAdjoinRootMap
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTraceAdjoinRootMap.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.map_trace_adjoinRoot_eq_trace_map : ∀ (R S : Type) [CommRing R] [CommRing S] (g : R →+* S) (h : R[X]), h.Monic → ∀ x : AdjoinRoot h, g (Algebra.trace R (AdjoinRoot h) x) = Algebra.trace S (AdjoinRoot (h.map g)) (AdjoinRoot.map g h (h.map g) dvd_rfl x) := by
  first | exact @GlobalTheory.trace_adjoinRoot_map | exact GlobalTheory.trace_adjoinRoot_map | (intros; apply GlobalTheory.trace_adjoinRoot_map <;> assumption)
